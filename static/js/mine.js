// select or deselect the search parameter boxes
var obj_boxes = ["obj_name_box", "obj_coord_box", 
                 "obj_discdate_box", "obj_host_box", 
                 "obj_hosttype_box", "obj_z_box"]
var spec_boxes = ["spec_type_box", "spec_snid_box", "spec_snid_sub_box", 
                  "spec_min_box", "spec_max_box", "spec_sn_box",
                  "spec_obsdate_box", "spec_inst_box", "spec_tel_box"]
var phot_boxes = ["phot_filt_box", "phot_npoints_box", "phot_tel_box"]
var img_boxes = ["img_filt_box", "img_inst_box", "img_tel_box"]
function srchCheckBoxes( select, which ) {
    for (i=0; i<which.length; i++) {
        document.getElementsByName(which[i])[0].checked = select;
    }
}

function dnldCheckBoxes( select, prefix ) {
    allBoxes = $('[name^="'+prefix+'"]')
    for (i=0; i<allBoxes.length; i++) {
        allBoxes[i].checked = select;
    }
}

function plotSpec( id ) {
    window.open("plotspec?specid="+id.toString(), '_blank');
}
function plotPhot( id ) {
    window.open("plotphot?photid="+id.toString(), '_blank');
}
function snidSpec( id ) {
    window.open("snid?specid="+id.toString(), '_blank');
}
function plotFits( id ) {
    window.open("plotfits?imgid="+id.toString(), '_blank');
}
function infoSpec( id ) {
    window.open("allinfo?specid="+id.toString(), '_blank');
}
function infoPhot( id ) {
    window.open("allinfo?photid="+id.toString(), '_blank');
}
function getOneSpec( id ) {
    window.open("download?id=ds:"+id.toString(), '_blank');
}
function getOnePhot( id ) {
    window.open("download?id=dp:"+id.toString(), '_blank');
}
function getOneImg( id ) {
    window.open("download?id=di:"+id.toString(), '_blank');
}
