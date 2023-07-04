interface module_iface 
    #(parameter TDATA_WIDTH = 128);
        logic [TDATA_WIDTH-1:0] tdata;
        logic tvalid;
        
        modport master(output tdata, output tvalid);
        modport slave(input tdata, input tvalid);
endinterface

interface tlast2out_iface 
    #(parameter TDATA_WIDTH = 128);
        logic [TDATA_WIDTH-1:0] tdata;
        logic tvalid;
        logic tlast;
        
        modport master(output tdata, output tvalid, output tlast);
        modport slave(input tdata, input tvalid, input tlast);
endinterface
