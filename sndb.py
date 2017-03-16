from flask import Flask,render_template,request,session,redirect,url_for,send_from_directory,flash,get_flashed_messages,make_response
from flask.ext.session import Session
from cStringIO import StringIO
from numpy.random import randint
import matplotlib as mpl 
mpl.use('Agg') # this work around lets mpl run without needing the X11 $DISPLAY variable set
from matplotlib.ticker import MultipleLocator
from matplotlib.backends.backend_agg import FigureCanvasAgg as FigureCanvas
import matplotlib.pyplot as plt
import mpld3
from glob import glob
from subprocess import call,Popen,PIPE
from dateutil import parser as dtparser
from copy import copy
import credentials as creds
import numpy as np
import pyfits as pf
import requests
import json
import MySQLdb
import MySQLdb.cursors
import os
import tarfile
import urllib
import datetime
import re

######################################################################
# GLOBAL VARIABLES
######################################################################

app = Flask(__name__)
SESSION_TYPE = 'redis'
app.config.from_object(__name__)
Session(app)

MAX_RESULTS = 250
TEMPDIR = creds.tempdir
ROOTDIR = creds.rootdir

######################################################################
# DATABASE HELPER FUNCTIONS
######################################################################

def get_cursor( un=None, pw=None ):
    """
    Returns a cursor to the DB if your credentials work out.
    """
    if (un==None) or (pw==None):
        un = session.get('un')
        pw = session.get('pw')
    try:
        DB = MySQLdb.connect(host=creds.host, user=un, passwd=pw, db=creds.db, cursorclass=MySQLdb.cursors.DictCursor)
    except:
        # hit here if the login credentials are bad or not given; log in using the defaults
        DB = MySQLdb.connect(host=creds.host, user=creds.user, passwd=creds.passwd, db=creds.db, cursorclass=MySQLdb.cursors.DictCursor)
    return DB.cursor()

def get_db_parser():
    """
    Returns a handle to the DB.literal function, which allows you to parse potentially harmful SQL code from users.
    """
    DB = MySQLdb.connect(host=creds.host, user=creds.user, passwd=creds.passwd, db=creds.db, cursorclass=MySQLdb.cursors.DictCursor)
    return DB.literal

def json_clean( res ):
    """
    Takes an input mysqldb response and converts any non-serializable objects 
     into a string.
    """
    for row in res:
        for k in row.keys():
            if type(row[k]) == datetime.date:
                row[k] = str(row[k])
    return res
    
def valid_login( un=None, pw=None ):
    """
    Verifies user against MYSQL database.
    """
    if (un==None) or (pw==None):
        un = session.get('un')
        pw = session.get('pw')
    try:
        DB = MySQLdb.connect(host=creds.host, user=un, passwd=pw, db=creds.db, cursorclass=MySQLdb.cursors.DictCursor)
        # success
        session['un'] = un
        session['pw'] = pw
        return True
    except:
        # invalid login
        return False

def construct_valid_sql( sql, formats ):
    """
    Constructs a valid sql query by inserting the string representation
     of formats into the sql query and returning the result.
    Emulates MySQLdb's "execute" functionality.
    """
    parser = get_db_parser()
    outsql = sql %tuple([parser(item) for item in formats])
    return outsql

def sql_format( messysql ):
    """
    Formats and simplifies SQL queries for easier reading. 
    """
    try:
        s = messysql.replace('WHERE','WHERE\n    ')
        s = s.replace('LIMIT','\nLIMIT')
        inparens = 0
        i = 0
        while True:
            if i == len(s):
                break
            if s[i] == '(':
                inparens +=1
            elif s[i] == ')':
                inparens -=1
            elif not inparens and s[i:i+3] == 'AND':
                s = s[:i]+'\n '+s[i:]
                i +=3
            i +=1
    except:
        raise SNDBError('ERROR: Your query does not seem to formed properly!')
    return s

def parse_logicals( string ):
    """
    Given an input string like '<300', produces the appropriate MySQL query string.
    """
    if '<' in string:
        val = float(re.search('[+-]?[0-9]*\.?[0-9]+', string).group())
        return '< %s', [val]
    elif '>' in string:
        val = float(re.search('[+-]?[0-9]*\.?[0-9]+', string).group())
        return '> %s', [val]
    elif ',' in string:
        vals = map(float, string.split(','))
        vals.sort()
        return 'BETWEEN %s AND %s', vals
    else:
        val = float(re.search('[+-]?[0-9]*\.?[0-9]+', string).group())
        return '= %s', [val]

######################################################################
# CONSTRUCTING SQL QUERIES
######################################################################

def construct_sql_obj( form ):
    """
    Takes in the flask/http request object and 
    constructs WHERE SQL statements to filter objects.
    Results of this function are intended to be used in conjunction with 
     results of the below photometry/spectra/image SQL Generators.
    """
    wheres = []
    formats = []
    
    # the object name handles REGEX and searches both ObjName and AltObjName
    if form.get('obj_name'):
        if form.get('obj_name_box'):
            op = 'REGEXP'
        else:
            op = '='
        # test both ObjName and AltObjName for multiple plausible formats
        wherestring = '( (ObjName '+op+' %s) OR (ObjName '+op+' %s) OR (AltObjName '+op+' %s) OR (AltObjName '+op+' %s) )'
        wheres.append(wherestring)
        searchname = urllib.unquote( form.get('obj_name') )
        formats.extend( [searchname, searchname.lower().replace('sn','SN '),
                         searchname, searchname.lower().replace('sn','SN ')] )
    
    # the other entries that have a REGEX option
    formtosql = {'obj_type': 'Type', 'obj_host':'Hostname', 'obj_hosttype': 'HostType'}
    for fname in formtosql:
        #if a form entry has been filled
        if form.get(fname):
            wherestring = '('+formtosql[fname]
            #if the REGEX box was checked next to the box
            if form.get(fname+"_box"):
                wherestring += ' REGEXP %s)'
            else:
                wherestring += ' = %s)'
            wheres.append(wherestring)
            formats.append(form.get(fname))
    
    formtosql = {'obj_discdate': 'DiscDate', 'obj_peakdate': 'PeakDate'}
    for fname in formtosql:
        if form.get(fname):
             # have this satisfy a range
             dstr = form.get(fname)
             if form.get(fname+"_box"):
                 dmin,dmax = dstr.split(',')
                 # interpret reasonable date inputs and put into SQL format
                 dmin = dtparser.parse( dmin )
                 dmin = '%d-%d-%d' %(dmin.year, dmin.month, dmin.day)
                 dmax = dtparser.parse( dmax )
                 dmax = '%d-%d-%d' %(dmax.year, dmax.month, dmax.day)
                 wheres.append( '('+formtosql[fname]+' BETWEEN DATE( %s ) AND DATE( %s ))' )
                 formats.extend( [dmin,dmax] )
             else:
                 dstr = dtparser.parse( dstr )
                 dstr = '%s-%s-%s'%(dstr.year, dstr.month, dstr.day)
                 wheres.append( '('+formtosql[fname]+' = DATE( %s ) )' )
                 formats.append( dstr )
    
    if form.get("obj_coord"):
        ra,dec = form.get("obj_coord").split(',')
        ra = parse_ra( ra )
        dec = parse_dec( dec )
        sr = form.get("obj_sr")
        # if sr is not given, assume 1 arcminute
        if not sr:
            sr = 60.0
        else:
            sr = float(sr)
        rmin,rmax, dmin,dmax = coord_lims( ra, dec, sr/3600.0 )
        wheres.append( '(RA BETWEEN %s AND %s) AND (Decl BETWEEN %s AND %s)' )
        formats.extend( [rmin,rmax, dmin,dmax] )

    if form.get("obj_z"):
        logics, vals = parse_logicals( form.get("obj_z") )
        # have it match to Redshift_SN OR Redshift_Gal
        wheres.append( '((Redshift_SN %s ) OR (Redshift_Gal %s ))'%(logics, logics) )
        formats.extend( vals+vals )
    
    sql = ' WHERE ' + ' AND '.join(wheres)
    
    return (sql, formats)

def construct_sql_spectra( form, objwheres, private=False ):
    """
    Takes in the flask/http request object and the output of construct_sql_obj, and constructs a sql statement
     for querying spectra.
     
    Values returned when selecting * from the spec view:
        objects.ObjName, objects.Type,
        spectra.SpecID, spectra.Min, spectra.Max, spectra.SNR, spectra.Reference, spectra.Filename, spectra.UT_Date,
        spectralruns.Instrument, spectralruns.Telescope
    """
    sql = "SELECT * FROM spec_view"
    #select from specanon view instead if not logged in. 
    if not private:
        sql+='_public'
    
    # include the object query components
    sql += objwheres[0]    
    formats = copy(objwheres[1]) # need to copy the list of object wheres in case performing a spectral and phot search

    wheres = []
    # the entries that have a REGEX option
    formtosql = {'spec_type': 'Spec_Type', 'spec_snid': 'SNID_Type', 'spec_snid_sub': 'SNID_Subtype', 'spec_inst' : 'Instrument', 'spec_tel' : 'Telescope'}
    for fname in formtosql:
        #if a form entry has been filled
        if form.get(fname):
            wherestring = '('+formtosql[fname]
            #if the REGEX box was checked next to the box
            if form.get(fname+"_box"):
                wherestring += ' REGEXP %s)'
            else:
                wherestring += ' = %s)'
            wheres.append(wherestring)
            formats.append(form.get(fname))    

    # the other entries
    formtosql = {'spec_min': 'Min', 'spec_max': 'Max', 'spec_sn': 'SNR',
                 'spec_delta_disc': 'PhaseDisc', 'spec_delta_peak': 'PhasePeak'}
    for fname in formtosql:
        if form.get(fname):
            logics, vals = parse_logicals( form.get(fname) )
            wheres.append( '( %s %s )'%(formtosql[fname], logics) )
            formats.extend( vals )
    
    if form.get("spec_obsdate"):
        # have this satisfy a range, and search against the date
        #  stored in the spectralruns table
        dstr = form.get("spec_obsdate")
        if form.get("spec_obsdate_box"):
            dmin,dmax = dstr.split(',')
            # interpret reasonable date inputs and put into SQL format
            dmin = dtparser.parse( dmin )
            dmin = '%d-%d-%d' %(dmin.year, dmin.month, dmin.day)
            dmax = dtparser.parse( dmax )
            dmax = '%d-%d-%d' %(dmax.year, dmax.month, dmax.day)
            wheres.append( '(FLOOR(UT_Date) BETWEEN DATE( %s ) AND DATE( %s ))' )
            formats.extend( [dmin,dmax] )
        else:
            # because the spectrum obsdates are stored as floats with fractional
            #  days, we need to query the database cleverly to match properly
            dstr = dtparser.parse( dstr )
            dmin = '%d-%d-%d' %(dstr.year, dstr.month, dstr.day)
            dmax = '%d-%d-%d' %(dstr.year, dstr.month, dstr.day+1)
            wheres.append( '(FLOOR(UT_Date) BETWEEN DATE( %s ) AND DATE( %s ))' )
            formats.extend( [dmin,dmax] )

    if wheres and objwheres[1]:
        sql += ' AND '
    sql += ' AND '.join(wheres)
    sql += ' LIMIT %d;'%MAX_RESULTS
    return (sql, formats)
    
def construct_sql_phot( form, objwheres, private=False ):
    """
    Takes in the flask/http request object and the output of construct_sql_obj and constructs a sql statement
     out of it for querying photometry files.
    
    Values currently returned when selecting * from phot:
        objects.ObjName, objects.Type,
        photometry.PhotID, photometry.Filename, photometry.Filters, photometry.FirstObs, photometry.LastObs, photometry.Telescopes,
        photometry.NPoints, photometry.Reference,
    """
    sql = "SELECT * FROM phot_view"
    # pull data from phot view if logged in, photanon if not. 
    if not private:
       sql += '_public'
    
    # include the object query components
    sql += objwheres[0]    
    formats = copy(objwheres[1]) # need to copy the list of object wheres in case performing a spectral and phot search
    
    wheres = []
    # the entries that have a REGEX option
    formtosql = {'phot_filt': 'Filters', 'phot_tel': 'Telescopes'}
    for fname in formtosql:
        #if a form entry has been filled
        if form.get(fname):
            wherestring = '('+formtosql[fname]
            #if the REGEX box was checked next to the box
            if form.get(fname+"_box"):
                wherestring += ' REGEXP %s)'
            else:
                wherestring += ' = %s)'
            wheres.append(wherestring)
            formats.append(form.get(fname))
    
    # the other entries
    if form.get("phot_npoints"):
        logics, vals = parse_logicals( form.get("phot_npoints") )
        wheres.append( '( NPoints %s )'%logics )
        formats.extend( vals )
    
    if wheres and objwheres[1]:
        sql += ' AND '
    sql += ' AND '.join(wheres) 
    sql += ' LIMIT %d;'%MAX_RESULTS
    return (sql, formats)

def construct_sql_img( form, private=False ):
    """
    Takes in the flask/http request object and constructs a sql statement
     out of it for querying images.

    NOT CURRENTLY USED - IMAGE SEARCH IS NOT CURRENTLY USED.
    """
    if not private:
        return ('','')
    imgpars = ["ImgID","Filename","Filepath","ObjName","RA","Decl","Date","Exposure","Filter","Instrument","Telescope"]
    sql = "SELECT %s FROM images" %','.join(imgpars)
    
    wheres = []
    formats = []
    
    # the entries that have a REGEX option
    formtosql = {'obj_name': 'ObjName', 'img_filt': 'Filter', 'img_inst': 'Instrument', 'img_tel' : 'Telescope'}
    for fname in formtosql:
        #if a form entry has been filled
        if form.get(fname):
            wherestring = '('+formtosql[fname]
            #if the REGEX box was checked next to the box
            if form.get(fname+"_box"):
                wherestring += ' REGEXP %s)'
            else:
                wherestring += ' = %s)'
            wheres.append(wherestring)
            formats.append(form.get(fname))    
    
    # the other entries
    if form.get("obj_coord"):
        ra,dec = form.get("obj_coord").split(',')
        ra = parse_ra( ra )
        dec = parse_dec( dec )
        sr = form.get("obj_sr")
        # if sr is not given, assume 1 arcminute
        if not sr:
            sr = 60.0
        else:
            sr = float(sr)
        rmin,rmax, dmin,dmax = coord_lims( ra, dec, sr/3600.0 )
        wheres.append('(RA BETWEEN %s AND %s) AND (Decl BETWEEN %s AND %s)')
        formats.extend( [rmin,rmax, dmin,dmax] )
    if form.get("img_obsdate"):
        # have this satisfy a range or, if given a single date, simply match against the date
        dstr = form.get("img_obsdate")
        if form.get("img_obsdate_box"):
            dmin,dmax = dstr.split(',')
            # interpret reasonable date inputs and put into SQL format
            dmin = dtparser.parse( dmin )
            dmin = '%d-%d-%d' %(dmin.year, dmin.month, dmin.day)
            dmax = dtparser.parse( dmax )
            dmax = '%d-%d-%d' %(dmax.year, dmax.month, dmax.day)
            wheres.append('(Date BETWEEN DATE( %s ) AND DATE( %s ))')
            formats.extend( [dmin, dmax] )
        else:
            dstr = dtparser.parse( dstr )
            dstr = '%d-%d-%d' %(dstr.year, dstr.month, dstr.day)
            wheres.append('(DATE( %s ) = FLOOR(UT_Date))') 
            formats.append(dstr)
    
    if wheres:
        sql += ' WHERE '
    sql += ' AND '.join(wheres)
    sql += ' LIMIT %d;'%MAX_RESULTS
    return (sql, formats)

def construct_sql_info( ID, which, private=False, objinfo=True ):
    """
    Given a SNDB specID or photId number and a flag for spectrum ('s') or photometry file ('p'),
     construct the sql query to get all info about a data file and the object it's associated with.
    """
    if which == 's':
        if objinfo:
            sql = "SELECT spectra.*,objects.*,objectinfo.*,spectralruns.* from spectra,objects,objectinfo,spectralruns WHERE "+\
                  "(spectra.ObjID = objects.ObjID) AND (objects.ObjID = objectinfo.ObjID) AND (spectra.RunID = spectralruns.RunID) AND (spectra.SpecID = %s)"
        else:
            sql = "SELECT spectra.*,objects.*,spectralruns.* from spectra,objects,spectralruns WHERE "+\
                  "(spectra.ObjID = objects.ObjID) AND (spectra.RunID = spectralruns.RunID) AND (spectra.SpecID = %s)"
    elif which == 'p':
        if objinfo:
            sql = "SELECT photometry.*,objects.*,objectinfo.* from photometry,objects,objectinfo WHERE "+\
                  "(photometry.ObjID = objects.ObjID) AND (objects.ObjID = objectinfo.ObjID) AND (photometry.PhotID = %s)"
        else:
            sql = "SELECT photometry.*,objects.* from photometry,objects WHERE "+\
                  "(photometry.ObjID = objects.ObjID) AND (photometry.PhotID = %s)"
    if not private:
        if which == 's':
            sql += ' AND (spectra.Public = 1)'
        elif which == 'p':
            sql += ' AND (photometry.Public = 1)'
    sql += ';'
    return (sql, [ID])

def construct_sql_download( IDs, which, private=False ):
    """
    Construct the sql query to get filenames for download.
     <IDs> must be a list of SpecID, ImgID, or PhotID, and <which> must
     be be one of [s,p,i]
    """
    if which == 's':
        sql = "SELECT Filepath,Filename FROM spectra WHERE ("+\
              " OR ".join(["(SpecID=%d)"%i for i in IDs])
    elif which == 'i':
        sql = "SELECT Filepath,Filename FROM images WHERE ("+\
               " OR ".join(["(ImgID=%d)"%i for i in IDs])
    elif which == 'p':
        sql = "SELECT Filepath,Filename FROM photometry WHERE ("+\
               " OR ".join(["(PhotID=%d)"%i for i in IDs])
    else:
        return
    if private:
        sql += ");"
    else:
        sql += ") AND (Public=1);"
    return sql

def run_query( sql, formats=None ):
    """
    Given an sql string, run that query and return the DB's response.
    """
    c = get_cursor()
    c.execute( sql, formats )
    res = json_clean( c.fetchmany(MAX_RESULTS) )
    c.close()
    if len(res) == 0:
        # using this error here may seem odd, but it makes everything consistent with downstream error handlers
        raise KeyError
    return res

######################################################################
# MISC HELPER FUNCTIONS
######################################################################

def coord_lims( ra, dec, sr ):
    """
    Returns a tuple of (rmin,rmax, dmin,dmax) given a central
     RA,Dec pair and a search radius (all in degrees).
    """
    # APPROXIMATE
    d1 = dec-sr
    d2 = dec+sr
    r1 = ra - sr/np.cos( np.deg2rad(dec) )
    r2 = ra + sr/np.cos( np.deg2rad(dec) )
    rmin,rmax = min([r1,r2]),max([r1,r2])
    dmin,dmax = min([d1,d2]),max([d1,d2])
    return (rmin,rmax, dmin,dmax)

def parse_ra( inn ):
    '''
    Parse input Right Ascension string, either decimal degrees or sexagesimal HH:MM:SS.SS (or similar variants).
    Returns decimal degrees.
    '''
    # if simple float, assume decimal degrees
    try:
        ra = float(inn)
        return ra
    except:
        # try to parse with phmsdms:
        res = parse_sexagesimal(inn)
        ra = 15.*( res['vals'][0] + res['vals'][1]/60. + res['vals'][2]/3600. )
        return ra

def parse_dec( inn ):
    '''
    Parse input Declination string, either decimal degrees or sexagesimal DD:MM:SS.SS (or similar variants).
    Returns decimal degrees.
    '''
    # if simple float, assume decimal degrees
    try:
        dec = float(inn)
        return dec
    except:
        # try to parse with phmsdms:
        res = parse_sexagesimal(inn)
        dec = res['sign']*( res['vals'][0] + res['vals'][1]/60. + res['vals'][2]/3600. )
        return dec

def parse_sexagesimal(hmsdms):
    """
    +++ Pulled from python package 'angles' +++
    Parse a string containing a sexagesimal number.

    This can handle several types of delimiters and will process
    reasonably valid strings. See examples.

    Parameters
    ----------
    hmsdms : str
        String containing a sexagesimal number.

    Returns
    -------
    d : dict

        parts : a 3 element list of floats
            The three parts of the sexagesimal number that were
            identified.
        vals : 3 element list of floats
            The numerical values of the three parts of the sexagesimal
            number.
        sign : int
            Sign of the sexagesimal number; 1 for positive and -1 for
            negative.
        units : {"degrees", "hours"}
            The units of the sexagesimal number. This is infered from
            the characters present in the string. If it a pure number
            then units is "degrees".
    """
    units = None
    sign = None
    # Floating point regex:
    # http://www.regular-expressions.info/floatingpoint.html
    #
    # pattern1: find a decimal number (int or float) and any
    # characters following it upto the next decimal number.  [^0-9\-+]*
    # => keep gathering elements until we get to a digit, a - or a
    # +. These three indicates the possible start of the next number.
    pattern1 = re.compile(r"([-+]?[0-9]*\.?[0-9]+[^0-9\-+]*)")
    # pattern2: find decimal number (int or float) in string.
    pattern2 = re.compile(r"([-+]?[0-9]*\.?[0-9]+)")
    hmsdms = hmsdms.lower()
    hdlist = pattern1.findall(hmsdms)
    parts = [None, None, None]

    def _fill_right_not_none():
        # Find the pos. where parts is not None. Next value must
        # be inserted to the right of this. If this is 2 then we have
        # already filled seconds part, raise exception. If this is 1
        # then fill 2. If this is 0 fill 1. If none of these then fill
        # 0.
        rp = reversed(parts)
        for i, j in enumerate(rp):
            if j is not None:
                break
        if  i == 0:
            # Seconds part already filled.
            raise ValueError("Invalid string.")
        elif i == 1:
            parts[2] = v
        elif i == 2:
            # Either parts[0] is None so fill it, or it is filled
            # and hence fill parts[1].
            if parts[0] is None:
                parts[0] = v
            else:
                parts[1] = v

    for valun in hdlist:
        try:
            # See if this is pure number.
            v = float(valun)
            # Sexagesimal part cannot be determined. So guess it by
            # seeing which all parts have already been identified.
            _fill_right_not_none()
        except ValueError:
            # Not a pure number. Infer sexagesimal part from the
            # suffix.
            if "hh" in valun or "h" in valun:
                m = pattern2.search(valun)
                parts[0] = float(valun[m.start():m.end()])
                units = "hours"
            if "dd" in valun or "d" in valun:
                m = pattern2.search(valun)
                parts[0] = float(valun[m.start():m.end()])
                units = "degrees"
            if "mm" in valun or "m" in valun:
                m = pattern2.search(valun)
                parts[1] = float(valun[m.start():m.end()])
            if "ss" in valun or "s" in valun:
                m = pattern2.search(valun)
                parts[2] = float(valun[m.start():m.end()])
            if "'" in valun:
                m = pattern2.search(valun)
                parts[1] = float(valun[m.start():m.end()])
            if '"' in valun:
                m = pattern2.search(valun)
                parts[2] = float(valun[m.start():m.end()])
            if ":" in valun:
                # Sexagesimal part cannot be determined. So guess it by
                # seeing which all parts have already been identified.
                v = valun.replace(":", "")
                v = float(v)
                _fill_right_not_none()
        if not units:
            units = "degrees"

    # Find sign. Only the first identified part can have a -ve sign.
    for i in parts:
        if i and i < 0.0:
            if sign is None:
                sign = -1
            else:
                raise ValueError("Only one number can be negative.")

    if sign is None:  # None of these are negative.
        sign = 1

    vals = [abs(i) if i is not None else 0.0 for i in parts]
    return dict(sign=sign, units=units, vals=vals, parts=parts)    
    
######################################################################
# INTERACTING WITH FILE SYSTEM
######################################################################

def prep_one_file( ID, which, private=False ):
    """
    Pulls a single file from the main data store and serves it to the user
     in a secure way.
    """
    sql = construct_sql_download( [ID], which, private=private )
    c = get_cursor()
    c.execute( sql )
    r = c.fetchone()
    c.close()
    fpath = ROOTDIR+r['Filepath']+'/'+r['Filename']
    newpath = TEMPDIR+r['Filename']
    os.system( 'cp %s %s'%(fpath,newpath) )
    return r['Filename']

def tar_all_files( IDs, which, private=False ):
    """
    Produces a tarfile of the spectra/photfiles indicated by IDs and
     returns the path to it.
    """
    sql = construct_sql_download( IDs, which, private=private )
    c = get_cursor()
    c.execute( sql )
    results = c.fetchmany(MAX_RESULTS)
    c.close()
    allfiles = [r['Filepath']+'/'+r['Filename'] for r in results]
    tarfname = prep_tarfile( allfiles )
    return tarfname

def prep_tarfile( allfiles ):
    """
    Creates a tarfile of filepaths given and returns the path to it.
    """
    fname = TEMPDIR+str(randint(100000))+'.tgz'
    tar = tarfile.open( name=fname, mode='w:gz' )
    for f in allfiles:
        tar.add( ROOTDIR+f, arcname=os.path.basename(f) )
    tar.close()
    return fname

def pretty_plot_phot(t, m, e, label=None, fig=None):
    '''
    Produces pretty photometry plot.
    t,m,e should all be 1d arrays.
    '''
    if fig==None:
        fig = plt.figure( figsize=(14,7), facecolor='w', edgecolor='k' )
        plt.xlabel('MJD')
        plt.ylabel('Magnitude')
        if len(t) > 1: # breaks on single phot points
            plt.gca().xaxis.set_minor_locator( MultipleLocator(5) )
            plt.grid(b=True, which='major', color='gray', linestyle='--')
        plt.gca().invert_yaxis()
    else:
        plt.figure( fig.number )
        fig = plt.gcf()
    # choose a nice color
    if label == 'clear':
        c = 'k'
    elif label == 'B':
        c = '#00447D'
    elif label == 'V':
        c = '#00902B'
    elif label == 'R':
        c = '#C21A00'
    elif label == 'I':
        c = '#C27000'
    else:
        c = '#474747'
    # now actually put them on the plot
    plt.errorbar(t, m, yerr=e, fmt='.', c=c, label=label)
    plt.legend(loc=1,title='')
    return fig

def pretty_plot_spectra(lam, flam, err=None, label=None, multi=False, label_coord=None, fig=None, binning=None):
    '''
    Produce pretty spectra plots.

    lam: wavelength (A expected)
    flam: flux (ergs/cm^2/sec/A expected)
    Both should be array-like, either 1D or 2D.
     If given 1D arrays, will plot a single spectrum.
     If given 2D arrays, first dimension should correspond to spectrum index.
    label: optional string to include as label
    multi: if True, expects first index of entries to be index, and places
           all plots together on a axis.
    label_coord: the x-coordinate at which to place the label
    fig: the figure to add this plot to
    binning: if set, bins the input arrays by that factor before plotting
    
    EDIT: for now, do not plot errors, since sometimes they seem very wrong.
    '''
    if binning != None:
        if multi:
            for i,lll in enumerate(lam):
                lam[i] = rebin1D( lll, binning )
            for i,fff in enumerate(flam):
                flam[i] = rebin1D( fff, binning )
            if err != None:
                for i,eee in enumerate(err):
                    err[i] = rebin1D( eee, binning )
        else:
            lam = rebin1D( lam, binning )
            flam = rebin1D( flam, binning )
            if err != None:
                err = rebin1D( err, binning )
        drawstyle='steps-mid'
    else:
        drawstyle='default'
    
    colors = {'red':'#ca0020',
        'blue':'#2b83ba',
        'black':'k',
        'grey':'#878787',
        'orange':'#bf812d',
        'green':'#006837'}

    spec_kwargs = dict( alpha=1., linewidth=1, drawstyle=drawstyle )
    err_kwargs = dict( interpolate=True, color=(0./256, 165./256, 256./256), alpha=.1 )
    if fig == None:
        fig = plt.figure( figsize=(14,7), facecolor='w', edgecolor='k' )
    ax = plt.subplot(1,1,1)

    if not multi:
        ax.plot( lam, flam, c=colors['blue'], **spec_kwargs )
        if err != None:
            # ax.fill_between( lam, flam+err, flam-err, **err_kwargs )
            pass
        if label != None:
            # put the label where requested, or at a reasonable spot if not requested
            if label_coord == None:
                lam_c = np.max(lam) - (np.max(lam)-np.mean(lam))/3.
            else:
                lam_c = label_coord
            i_c = np.argmin( np.abs(lam-lam_c) )
            flam_c = np.max( flam[i_c:i_c+100] )
            ax.annotate( label, (lam_c, flam_c) )
    else:
        # normalize and define an offset for each spectrum
        for iii in range( len(lam) ):
            # use only a subset of the spectrum to set the scaling
            m = (lam[iii] > 4000) & (lam[iii] < 9000)
            flam[iii] = (flam[iii] - np.mean(flam[iii][m])) / np.std(flam[iii][m])
        offset = 2.0
        for iii in range( len(lam) ):
            l, f = lam[iii], flam[iii]+(iii*offset)
            c = colors[ colors.keys()[iii%len(colors)] ]
            ax.plot( l, f, c=c, **spec_kwargs )
            if err != None:
                e = err[iii]
                if e != None:
                    # ax.fill_between( l, f+e, f-e, **err_kwargs )
                    pass
            if label != None:
                # put the label where requested, or at a reasonable spot if not requested
                if label_coord == None:
                    lam_c = np.max(l) - (np.max(l)-np.mean(l))/3.
                else:
                    lam_c = label_coord[iii]
                i_c = np.argmin( np.abs(l-lam_c) )
                flam_c = np.max( f[i_c:i_c+100] )
                ax.annotate( label[iii], (lam_c, flam_c) )
        # set the plot limits by hand
        plt.ylim( -offset, offset*(iii+2) )

    plt.xlabel('Observed Wavelength (A)')
    if multi:
        plt.ylabel('Observed Flux + Constant')
    else:
        plt.ylabel('Observed Flux')
    plt.gca().xaxis.set_minor_locator( MultipleLocator(100) )
    plt.grid(b=True, which='major', color='gray', linestyle='--')
    
    return fig

def create_spec_plot( pathname, second=None, title=None, multi=False ):
    """
    Creates a spectrum plot and serves it in a web-friendly form.
    """
    if not multi:
        fig = pretty_plot_spectra(*np.loadtxt(pathname, unpack=True) )
        if second != None:
            d2 = np.loadtxt( second )
            plt.plot( d2[:,0], d2[:,1], c='#C21A00', lw=2 )
    else:
        # pull all the data arrays from file
        flams, lams, labels = [],[],[]
        for path in pathname:
            label = os.path.basename(path)
            labels.append( label )
            d = np.loadtxt( path )
            f,l = d[:,0],d[:,1]
            flams.append(f)
            lams.append(l)
        fig = pretty_plot_spectra( flams, lams, multi=True, label=labels )
    if title != None:
        plt.title( title )
    return fig

def create_phot_plot( pathname, title=None ):
    """
    Creates a lightcurve plot and serves it in a web-friendly form.
    """
    data = parse_photfile( pathname )
    for i,passband in enumerate(data.keys()):
        d = np.array(data[passband])
        if i==0:
            fig = pretty_plot_phot( d[:,0], d[:,1], d[:,2], label=passband  )
        else:
            fig = pretty_plot_phot( d[:,0], d[:,1], d[:,2], label=passband, fig=fig  )
    if title != None:
        plt.title( title )
    return fig

def create_fits_image_plot( pathname, title=None ):
    """
    Creates a plot of a fits image and serves it in a web-friendly form.
    """
    try:
        hdu = pf.open( pathname )
    except:
        # probably a zcatted image
        p = Popen(["zcat", pathname], stdout=PIPE)
        hdu = pf.open( StringIO(p.communicate()[0]) )
    hdu.verify('fix')

    fig = plt.figure( figsize=(8,7), facecolor='w', edgecolor='k' )
    plt.imshow( np.log10( hdu[0].data ), cmap='gray_r' )
    plt.xlabel('X (pixels)')
    plt.ylabel('Y (pixels)')
    if title != None:
        plt.title( title )
    return fig

def parse_photfile( pathname ):
    """
    Parse a flipper-format photometry file.
    """
    lines = open( pathname, 'r' ).readlines()
    out = {}
    for l in lines:
        if l[0] == '#':
            continue
        l = l.split()
        mjd = float(l[0])
        mag = float(l[1])
        err = float(l[2])
        filt = l[4]
        if filt not in out.keys():
            out[filt] = []
        out[filt].append( [mjd,mag,err] )
    return out

def run_snid( infile ):
    """
    Runs a snid comparision.
    """
    os.chdir( TEMPDIR )
    cmd = ['/usr/local/bin/snid','inter=0','plot=0','fluxout=5',infile]
    o,e = Popen(cmd, stdout=PIPE,stderr=PIPE).communicate()
    return o,e

def pull_snid_template( snidcomp ):
    """
    Pulls the template name from the beginning of a snid comparision file.
    """
    return open( snidcomp,'r' ).readline().strip('#').strip()

######################################################################
# PAGE VIEWS
######################################################################

@app.route("/search", methods=["GET", "POST"])
@app.route("/", methods=["GET", "POST"])
def search():
    # just serve the search page if this is a get request
    if request.method == 'GET':
        return render_template('search.html', private=valid_login() )
    # handle the request if this is a post request
    elif request.method == 'POST':
        # see if this is a login attempt
        if request.form.get('submitButton') == 'sign_in':
            # this is a login attempt: check to see if the un/pw is good
            if valid_login(request.form['username'],
                           request.form['password']):
                flash( "Login successful!" )
                return render_template('search.html', private=valid_login() )
            else:
                raise SNDBError("Error: Bad login credentials!")
        elif request.form.get('submitButton') == 'sign_out':
            # user wants to log out; remove their credentials from their session cookie
            session.pop('un')
            session.pop('pw')
            flash( "Successfully logged out." )
            return render_template('search.html', private=valid_login() )
        else:
            # this is a search request or a sql query request
            if (not request.form.get("return_spec")) and (not request.form.get("return_phot")) and (not request.form.get("return_img")):
                raise SNDBError("Error: Malformed search! You must choose something to return.")
            sqlstr = ''
            obj_wheres = construct_sql_obj(request.form)
            if request.form.get("return_spec"):
                # construct the spectral search string and save it in the session cookie
                session["spec_sql"] = construct_sql_spectra( request.form, obj_wheres, private=valid_login() )
                sqlstr += sql_format( construct_valid_sql(*session["spec_sql"]) ) + '\n\n'
            else:
                # clear the search history if you're performing a new one
                session.pop("spec_sql", None)
            if request.form.get("return_phot"):
                # construct the photometric search string and save it in the session cookie
                session["phot_sql"] = construct_sql_phot( request.form, obj_wheres, private=valid_login() )
                sqlstr += sql_format( construct_valid_sql(*session["phot_sql"]) ) + '\n\n'
            else:
                session.pop("phot_sql", None)
            # IMAGE SEARCHES ARE NO LONGER IMPLEMENTED BUT THE BELOW CODE WORKS IF WE WANT TO RE-INCLUDE THEM.
            if request.form.get("return_img") and valid_login(): #only allow image searches for private searches
                session["img_sql"] = construct_sql_img( request.form, private=True )
                sqlstr += sql_format( construct_valid_sql(*session["img_sql"]) ) + '\n\n'
            else:
                session.pop("img_sql", None)
            if request.form.get('getsqlButton') == 'get_sql':
                # show the user the sql query they constructed
                return render_template('search.html', private=valid_login(), sqlstr=sqlstr)
            else:
                # the user wants to actually run the search
                return redirect(url_for('results'))

@app.route("/results", methods=["GET", "POST"])
def results():
    if request.method == 'GET':
        # user just landed here; perform the search that is saved in their session cookie and present the results!
        try:
            specresults = run_query( *session["spec_sql"] )
            if len(specresults) == MAX_RESULTS:
                specmaxed = MAX_RESULTS
            else:
                specmaxed = False
            if len(specresults) == 0:
                specresults = None
        except KeyError:
            specresults = None
            specmaxed = False
        except MySQLdb.ProgrammingError:
            # any SNDBError will send the user back to the search page with an error message.
            raise SNDBError( 'ERROR: Your search for spectra was malformed or does not have enough constraints!' )
        try:
            photresults = run_query( *session["phot_sql"] )
            if len(photresults) == MAX_RESULTS:
                photmaxed = MAX_RESULTS
            else:
                photmaxed = False
            if len(photresults) == 0:
                photresults = None
        except KeyError:
            photresults = None
            photmaxed = False
        except MySQLdb.ProgrammingError:
            raise SNDBError( 'ERROR: Your search for photometry was malformed or does not have enough constraints!' )
        # IMAGE SEARCH IS CURRENTLY NOT USED, BUT THE BELOW CODE WORKS IF WE WANT TO RE-IMPLEMENT IMAGE SEARCHES.
        try:
            imgresults = run_query( *session["img_sql"] )
            if len(imgresults) == MAX_RESULTS:
                imgmaxed = MAX_RESULTS
            else:
                imgmaxed = False
            if len(imgresults) == 0:
                imgresults = None
        except KeyError:
            imgresults = None
            imgmaxed = False
        except MySQLdb.ProgrammingError:
            raise SNDBError( 'ERROR: Your search for images was malformed or does not have enough constraints!' )
        if (imgresults == None) and (photresults == None) and (specresults == None):
            raise SNDBError("Error: No results found.")
        else:
            # after you've run all the searches, and if there are any results, show them!
            return render_template('results.html', specresults=specresults, specmaxed=specmaxed,
                                               photresults=photresults, photmaxed=photmaxed,
                                               imgresults=imgresults, imgmaxed=imgmaxed,
                                               private=valid_login() )
    else:
        allIDs = []
        if request.form.get('submitButton') == 'ds:':
            # trying to download spectra
            for item in request.form:
                if 'ds:' in item:
                    allIDs.append( int(item[3:]) )
            fname = tar_all_files( allIDs, 's', private=valid_login() )
            return send_from_directory(TEMPDIR, os.path.basename(fname), as_attachment=True, attachment_filename='SNDB_spectra.tgz' )
        if request.form.get('submitButton') == 'di:':
            # trying to download images NOT CURRENTLY USED
            for item in request.form:
                if 'di:' in item:
                    allIDs.append( int(item[3:]) )
            fname = tar_all_files( allIDs, 'i', private=valid_login() )
            return send_from_directory(TEMPDIR, os.path.basename(fname), as_attachment=True, attachment_filename='SNDB_images.tgz' )
        if request.form.get('submitButton') == 'dp:':
            # trying to download photometry
            for item in request.form:
                if 'dp:' in item:
                    allIDs.append( int(item[3:]) )
            fname = tar_all_files( allIDs, 'p', private=valid_login() )
            return send_from_directory(TEMPDIR, os.path.basename(fname), as_attachment=True, attachment_filename='SNDB_photometry.tgz' )

@app.route("/object", methods=["GET"])
def object():
    """
    Render a page that displays all of the info we have on an object,
     all at one place.
    """
    objname = urllib.unquote( request.query_string )
    obj_wheres = construct_sql_obj( {'obj_name':objname} )
    try:
        specresults = list(run_query( *construct_sql_spectra( {}, obj_wheres, private=valid_login() ) ))
        ra,dec = specresults[0]['RA'],specresults[0]['Decl']
    except KeyError:
        specresults = []
    try:
        photresults = list(run_query( *construct_sql_phot( {}, obj_wheres, private=valid_login() ) ))
        ra,dec = photresults[0]['RA'],photresults[0]['Decl']
    except KeyError:
        photresults = []
    if (not specresults) and (not photresults):
        raise SNDBError( "Error: No results found." )
    plots = []
    if specresults:
        # produce spectra plot
        specresults.sort( key=lambda x: x['UT_Date'], reverse=True )
        specIDs = [s['SpecID'] for s in specresults]
        # query for all the filepaths
        filepaths = []
        for ID in specIDs:
            sql = construct_sql_download( [int(ID)], 's', private=valid_login() )
            c = get_cursor()
            c.execute( sql )
            res = c.fetchone()
            c.close()
            filepath = ROOTDIR + res['Filepath']+'/'+res['Filename']
            filepaths.append(filepath)
        fig = create_spec_plot( filepaths, multi=True )
        plot = {'id':'p1', 'json':json.dumps(mpld3.fig_to_dict(fig))}
        plots.append(plot)
    if photresults:
        # produce photometry plot; assume there's only one
        PhotID = photresults[0]['PhotID']
        sql = construct_sql_download( [int(PhotID)], 'p', private=valid_login() )
        c = get_cursor()
        c.execute( sql )
        res = c.fetchone()
        c.close()
        filepath = ROOTDIR + res['Filepath']+'/'+res['Filename']
        fig = create_phot_plot( filepath )
        plot = {'id':'p2', 'json':json.dumps(mpld3.fig_to_dict(fig))}
        plots.append(plot)
    return render_template('object.html', plots=plots, private=valid_login(), ObjName=objname, 
                                          specresults=specresults, photresults=photresults,
                                          ObjRA=ra, ObjDecl=dec)

@app.route("/info", methods=["GET"])
def info():
    # return the "more info" web page
    return render_template("info.html", webmaster_email=creds.email)

@app.route("/direct", methods=["GET"])
def direct():
    """
    Offer up direct links to search results fron the URL (i.e. an API of sorts).
     Given any keyword and value pair in the url, will return a results page with
     the appropriate search results.

    For example:
     /sndb/direct?return_spec=True&spec_obsdate=2015-08-23
      --- returns all spectra observed on the night of Aug. 23, 2015 (UT)
     /sndb/direct?return_spec=True&return_phot=True&obj_name=SN 2011fe
      --- returns all spectra and photometry of SN 2011fe
    """
    direct_request = request.args
    obj_wheres = construct_sql_obj( direct_request )
    if direct_request.get("return_spec"):
        session["spec_sql"] = construct_sql_spectra( direct_request, obj_wheres, private=valid_login() )
    else:
        session.pop("spec_sql", None)
    if direct_request.get("return_phot"):
        session["phot_sql"] = construct_sql_phot( direct_request, obj_wheres, private=valid_login() )
    else:
        session.pop("phot_sql", None)
    if direct_request.get("return_img") and valid_login(): #only allow image searches for private searches
        session["img_sql"] = construct_sql_img( direct_request, private=True )
    else:
        session.pop("img_sql", None)
    return redirect(url_for('results'))
    
@app.route("/download", methods=["GET"])
def download():
    """
    The internal page that directs the user's browser to files requested for download.
    """
    ID = request.args.get('id')
    if 'ds:' in ID:
        return send_from_directory( TEMPDIR, prep_one_file(int(ID[3:]), 's', private=valid_login()), as_attachment=True )
    elif 'dp:' in ID:
        return send_from_directory( TEMPDIR, prep_one_file(int(ID[3:]), 'p', private=valid_login()), as_attachment=True )
    elif 'di:' in ID:
        return send_from_directory( TEMPDIR, prep_one_file(int(ID[3:]), 'i', private=valid_login()), as_attachment=True )
    elif ID == 'allpubspec':
        # provide a json list of all public spectra available
        c = get_cursor()
        sql = "SELECT * FROM spec_view_public"
        c.execute( sql )
        result = json.dumps( json_clean( c.fetchall() ), indent=2 )
        c.close()
        response = make_response(result)
        response.headers["Content-Disposition"] = "attachment; filename=publicSpectra.json"
        return response
    elif ID == 'allpubphot':
        # provide a json list of all public photometry available
        c = get_cursor()
        sql = "SELECT * FROM phot_view_public"
        c.execute( sql )
        result = json.dumps( json_clean( c.fetchall() ), indent=2 )
        c.close()
        response = make_response(result)
        response.headers["Content-Disposition"] = "attachment; filename=publicPhotometry.json"
        return response
        
@app.route("/plotspec", methods=["GET"])
def plot_one_spec():
    """
    Proffers up the requested plot of a spectrum.
    """
    SpecID = request.args.get('specid')
    sql = construct_sql_download( [int(SpecID)], 's', private=valid_login() )
    c = get_cursor()
    c.execute( sql )
    res = c.fetchone()
    c.close()
    filepath = ROOTDIR + res['Filepath']+'/'+res['Filename']
    fig = create_spec_plot( filepath, title=res['Filename'] )
    plot = {'id':'p1', 'json':json.dumps(mpld3.fig_to_dict(fig))}
    return render_template('base.html', plots=[plot], private=valid_login())
    
@app.route("/plotphot", methods=["GET"])
def plot_one_phot():
    """
    Proffers up the requested plot of a lightcurve.
    """
    PhotID = request.args.get('photid')
    sql = construct_sql_download( [int(PhotID)], 'p', private=valid_login() )
    c = get_cursor()
    c.execute( sql )
    res = c.fetchone()
    c.close()
    filepath = ROOTDIR + res['Filepath']+'/'+res['Filename']
    fig = create_phot_plot( filepath, title=res['Filename'] )
    # get rid of the box zoom, which doesn't work well
    mpld3.plugins.clear(fig)
    mpld3.plugins.connect(fig, mpld3.plugins.Reset(), mpld3.plugins.Zoom())
    plot = {'id':'p1', 'json':json.dumps(mpld3.fig_to_dict(fig))}
    return render_template('base.html', plots=[plot], private=valid_login())

@app.route("/plotfits", methods=["GET"])
def plot_one_fits():
    """
    Proffers up the requested fits image as a python plot.
    """
    ImgID = request.args.get('imgid')
    sql = construct_sql_download( [int(ImgID)], 'i', private=valid_login() )
    c = get_cursor()
    c.execute( sql )
    res = c.fetchone()
    c.close()
    filepath = ROOTDIR + res['Filepath']+'/'+res['Filename']
    fig = create_fits_image_plot( filepath, title=res['Filename'] )
    # get rid of the box zoom, which doesn't work well, and add other plugins
    mpld3.plugins.clear(fig)
    mpld3.plugins.connect(fig, mpld3.plugins.Reset(), mpld3.plugins.Zoom(), mpld3.plugins.MousePosition(fontsize=14))
    plot = {'id':'p1', 'json':json.dumps(mpld3.fig_to_dict(fig))}
    return render_template('base.html', plots=[plot], private=valid_login())

@app.route("/snid", methods=["GET"])
def snid_one():
    """
    SNIDs the requested spectrum, plots up the results, and also
     shows the output SNID file.
    """
    SpecID = request.args.get('specid')
    sql = construct_sql_download( [int(SpecID)], 's', private=valid_login() )
    c = get_cursor()
    c.execute( sql )
    res = c.fetchone()
    c.close()
    filepath = ROOTDIR + res['Filepath']+'/'+res['Filename']
    o,e = run_snid( filepath )
    if e:
        # snid failed
        raise SNDBError( 'SNID failure! Sorry.' )
    snid_fname = os.path.splitext(res['Filename'])[0]
    fluxed_spec = TEMPDIR+'%s_snidflux.dat'%snid_fname
    plots = []
    templates = glob( TEMPDIR+'%s_comp000?_snidflux.dat'%snid_fname )
    templates.sort()
    for i,f in enumerate(templates):
        title = pull_snid_template( f )
        fig = create_spec_plot( pathname=fluxed_spec, second=f, title=title )
        plot = {'id':'p%d'%i, 'json':json.dumps(mpld3.fig_to_dict(fig))}
        plots.append( plot )
    foutput = TEMPDIR+'%s_snid.output'%snid_fname
    snid_output = open(foutput,'r').read()
    return render_template('base.html', title='SNID: %s'%res['Filename'], private=valid_login(), plots=plots, snid_output=snid_output)

@app.route("/allinfo", methods=["GET"])
def all_info():
    """
    Proffers up all info associated with a lightcurve or spectrum file, including
     all info on the associated object.
    """
    SpecID = request.args.get('specid')
    PhotID = request.args.get('photid')
    if SpecID:
        i = int(SpecID)
        which = 's'
    elif PhotID:
        i = int(PhotID)
        which = 'p'
    else:
        raise SNDBError('Invalid info request.')
    
    c = get_cursor()
    sql,fmt = construct_sql_info( i, which, private=valid_login() )
    c.execute( sql, fmt )
    res = json_clean( c.fetchmany(MAX_RESULTS) )
    if not res:
        # probably an object without an objectinfo entry
        sql,fmt = construct_sql_info( int(SpecID), 's', objinfo=False, private=valid_login() )
        c.execute( sql, fmt )
        res = json_clean( c.fetchmany(MAX_RESULTS) )
    c.close()
    info = json.dumps(res, indent=2)
    return render_template('base.html', title=res[0]['Filename'], private=valid_login(), info=info)
    

######################################################################
# ERROR HANDLING
######################################################################
# set this to True to enable the Flask error handler and pass through all errors to it.
debug_mode = False

# a custom internal error class we can call in the code
class SNDBError(Exception):
    pass

if not debug_mode:
    # handle internal errors
    @app.errorhandler(SNDBError)
    def errorhandler(error):
        flash( error.args[0] )
        return redirect(url_for('search'))
    #@app.errorhandler(Exception)
    def errorhandler(error):
        flash( 'Error! Something went wrong ...' )
        return redirect(url_for('search'))
    # and handle a few HTTP errors
    @app.errorhandler(404)
    def errorhandler(error):
        flash( 'Error! Page not found.' )
        return redirect(url_for('search'))
    @app.errorhandler(500)
    def errorhandler(error):
        flash( 'Error! Something went wrong...' )
        return redirect(url_for('search'))

######################################################################
# RUNTIME
######################################################################

if __name__ == "__main__":
    if debug_mode:
        app.debug = True
        app.run(port=5001)
    else:
        app.debug = False
        app.run(port=5000)
