AttachSpec("ModFrmGL2.spec");

import "../csg24.dat/csg21-lev304.dat" : L21_304;


import "congruence.m" : LoadGroups, qExpansionBasisShimura;
import "congruence.m" : LoadGroupsByGenus;
import "congruence.m" : write_qexps;

import "ModSym/Box.m" : testBoxSingle;

grps := LoadGroups(L21_304);
grps_by_genus := LoadGroupsByGenus(L21_304);

degs := [1..6];

genera := [d*(d+1) div 2 : d in degs];

grps_g := AssociativeArray();

for g in genera do
    grps_g[g] := [grps[name] : name in grps_by_genus[g]];
end for;
/*
grps_g[3] := [grps[name] : name in grps_by_genus[3]];
grps_g[6] := [grps[name] : name in grps_by_genus[6]];
grps_g[10] := [grps[name] : name in grps_by_genus[10]];
grps_g[15] := [grps[name] : name in grps_by_genus[15]];
*/

// groups of Shimura type for these genera
shim := AssociativeArray();

shim[1] := [ Strings() | "6F1", "7B1", "8F1", "8K1", "9C1", "9H1", "10G1", "10K1", "11A1", 
"11D1", "12P1", "12S1", "12V1", "14C1", "14H1", "15C1", "15G1", "15I1", "16E1", 
"16M1", "17A1", "17B1", "17C1", "18J1", "19A1", "19B1", "20D1", "20H1", "21B1", 
"21F1", "24G1", "24J1", "27A1", "27C1", "32A1", "32E1", "36C1", "49A1" ];
shim[3] := [ Strings() | "7A3", "8A3", "12O3", "12K3", "15E3", "16H3", "20J3", "20S3", 
"21D3", "24V3", "24X3", "24Y3", "30K3", "32J3", "33C3", "34C3", "35A3", "36K3", "39A3", 
"40F3", "41A3", "43A3", "45D3", "48J3", "49A3", "64B3" ];

shim[6] :=  [ "11A6", "22C6", "31A6", "31B6",
            "58A6", "71A6", "79A6", "121A6" ];
shim[10] :=  [ "9A10", "18E10", "18M10", "26D10", "27B10", "28D10", "36Q10",
             "37A10", "38A10", "46A10", "54A10", "54I10", "81A10", "86A10"
             , "92A10", "108F10", "127A10" ];
shim[15] := [  "35C15", "40W15", "40X15", "43A15", "51A15", "60AC15", "60AD15", 
	     "67A15", "68D15", "80R15", "80T15", "85A15", "85B15", "102C15", "110A15", 
	     "136D15", "141A15", "153A15", "155A15", "161A15", "175A15", "179A15",
	     "193A15" ];
shim[21] := [ Strings() | "16C21", "21C21", "24A21", "28M21", "30G21", "32F21", 
			  "33C21", "34A21", "35B21", "36F21", "39B21", "41A21", "42H21", "45F21", 
			  "48CE21", "52C21", "55B21", "56L21", "56M21", "64F21", "65A21", "69A21", 
			  "72AC21", "78C21", "84Q21", "90O21", "91A21", "91B21", "92A21", "96BA21", 
			  "97A21", "104B21", "111A21", "112E21", "115A21", "117A21", "119A21", "128F21", 
			  "133B21", "137A21", "138A21", "147B21", "154B21", "165B21", "178A21", "184A21", 
			  "192P21", "201A21", "207A21", "215A21", "245A21", "247A21", "251A21", "256A21", 
			  "257A21" ];

filtered := AssociativeArray();

filtered[1] := [ "6A1", "6B1", "6C1", "6D1", "6E1", "6F1", "7A1", "7B1", "7C1", 
"8A1", "8B1", "8C1", "8F1", "8G1", "8I1", "8K1", "9A1", "9C1", "9D1", "9E1", 
"9G1", "9H1", "10A1", "10B1", "10C1", "10D1", "10E1", "10F1", "10G1", "10H1", 
"10I1", "10K1", "11A1", "11B1", "11C1", "11D1", "12B1", "12C1", "12F1", "12J1", 
"12K1", "12L1", "12M1", "12P1", "12S1", "12T1", "12V1", "14C1", "14E1", "14G1", 
"14H1", "15A1", "15B1", "15C1", "15D1", "15E1", "15F1", "15G1", "15H1", "15I1", 
"16A1", "16B1", "16C1", "16D1", "16E1", "16F1", "16G1", "16H1", "16I1", "16J1", 
"16M1", "17A1", "17B1", "17C1", "18A1", "18C1", "18E1", "18F1", "18G1", "18H1", 
"18I1", "18J1", "19A1", "19B1", "20D1", "20E1", "20H1", "20I1", "21B1", "21E1", 
"21F1", "24C1", "24D1", "24E1", "24G1", "24H1", "24J1", "26A1", "26B1", "27A1", 
"27B1", "27C1", "30C1", "30D1", "32A1", "32E1", "36C1", "49A1" ];

filtered[3] := ["7A3", "8B3", "8A3", "9A3", "10B3", "10C3", "10A3", "12P3", 
"12F3", "12G3", "12D3", "12E3", "12A3", "12N3", "12O3", "12L3", "12J3", "12K3", 
"12I3", "13B3", "13C3", "13A3", "14D3", "14C3", "14A3", "15H3", "15F3", "15G3", 
"15E3", "15B3", "15C3", "15A3", "16R3", "16S3", "16F3", "16D3", "16E3", "16B3", 
"16C3", "16A3", "16N3", "16O3", "16L3", "16J3", "16K3", "16H3", "16I3", "18A3", 
"18J3", "18K3", "18H3", "18I3", "18F3", "18G3", "18D3", "20F3", "20G3", "20E3", 
"20A3", "20L3", "20J3", "20K3", "20H3", "20I3", "20T3", "20R3", "20S3", "20P3", 
"21D3", "21C3", "21A3", "24B3", "24C3", "24A3", "24N3", "24O3", "24L3", "24K3", 
"24H3", "24I3", "24V3", "24W3", "24U3", "24P3", "24Q3", "24Z3", "24X3", "24Y3", 
"24AC3", "24AA3", "26A3", "27C3", "27A3", "28C3", "30F3", "30G3", "30D3", 
"30B3", "30A3", "30J3", "30K3", "30H3", "30I3", "32C3", "32A3", "32N3", "32O3", 
"32L3", "32M3", "32J3", "32K3", "32P3", "32B3", "33C3", "33A3", "34B3", "34C3", 
"34A3", "35A3", "36G3", "36D3", "36E3", "36A3", "36J3", "36K3", "36I3", "39A3", 
"40F3", "40G3", "40D3", "40E3", "40C3", "40J3", "40H3", "41A3", "42D3", "42E3", 
"43A3", "45D3", "45B3", "45A3", "48F3", "48G3", "48D3", "48E3", "48C3", "48L3", 
"48M3", "48J3", "48K3", "48H3", "48I3", "49A3", "50A3", "51A3", "52B3", "54A3", 
"64B3", "64A3", "72A3" ];

    filtered[6] := [ "10A6", "11A6", "14B6", "17A6", "18A6", "18B6", "18C6", "20C6", 
"20D6", "21B6", "21C6", "22A6", "22B6", "22C6", "24D6", "24G6", "27A6", "28D6", 
"28E6", "28G6", "28I6", "30A6", "30B6", "30C6", "30D6", "30E6", "31A6", "31B6", 
"32A6", "32B6", "35E6", "36C6", "36D6", "36E6", "36F6", "36J6", "36K6", "39A6", 
"45A6", "45C6", "45D6", "48A6", "48B6", "48C6", "48D6", "48I6", "48J6", "50E6", 
"52A6", "54A6", "54B6", "56D6", "56E6", "58A6", "60B6", "60C6", "60E6", "60F6", 
"63A6", "66B6", "66D6", "69A6", "71A6", "72B6", "72C6", "72D6", "78A6", "79A6", 
			   "86A6", "87A6", "90B6", "90C6", "100A6", "121A6" ];
    
    filtered[10] := [ Strings() | "9A10", "15A10", "15B10", "18A10", "18B10", "18C10", "18D10", 
"18E10", "18F10", "18G10", "18H10", "18L10", "18M10", "20A10", "20B10", "20C10",
"20D10", "20E10", "20F10", "21A10", "22A10", "24A10", "24B10", "25A10", "26A10",
"26D10", "26E10", "27B10", "28C10", "28D10", "30A10", "30B10", "30C10", "30F10",
"30H10", "32B10", "33B10", "33C10", "36A10", "36B10", "36C10", "36G10", "36I10",
"36J10", "36K10", "36M10", "36N10", "36O10", "36Q10", "36R10", "36S10", "37A10",
"38A10", "39B10", "40C10", "40D10", "40E10", "40F10", "40G10", "42A10", "42D10",
"42E10", "42G10", "42H10", "42I10", "42K10", "44B10", "44C10", "45A10", "45B10",
"46A10", "48A10", "48B10", "48C10", "48D10", "50A10", "52A10", "54A10", "54B10",
"54C10", "54E10", "54G10", "54I10", "56F10", "60C10", "72A10", "72B10", "72C10",
"72D10", "74A10", "75A10", "76A10", "78A10", "80A10", "80B10", "81A10", "84B10",
"84C10", "86A10", "88B10", "88C10", "90A10", "90D10", "90E10", "90F10", "92A10",
"96A10", "96B10", "100A10", "105A10", "108A10", "108F10", "110A10", "114A10", 
			     "114B10", "115A10", "118A10", "127A10", "134A10", "150A10" ];
    
filtered[15] := [ Strings() | "14A15", "17A15", "20A15", "20D15", "20E15", 
"20G15", "21A15", "21B15", "23A15", "24A15", "24B15", "24D15", "24E15", "24F15",
"24G15", "24H15", "24I15", "24J15", "24M15", "24N15", "24Q15", "24R15", "26A15",
"28C15", "28D15", "28E15", "28F15", "30A15", "30B15", "30C15", "30E15", "30F15",
"34A15", "35A15", "35B15", "35C15", "35D15", "36A15", "36B15", "36C15", "36D15",
"39A15", "40B15", "40C15", "40D15", "40E15", "40F15", "40G15", "40H15", "40I15",
"40L15", "40M15", "40N15", "40O15", "40R15", "40S15", "40U15", "40V15", "40W15",
"40X15", "40Y15", "40Z15", "40AA15", "40AB15", "40AD15", "40AE15", "40AF15", 
"42A15", "42B15", "42C15", "42D15", "43A15", "45A15", "45B15", "45D15", "48E15",
"48F15", "48G15", "48H15", "48I15", "48K15", "48L15", "48M15", "48N15", "48O15",
"48P15", "48Q15", "48R15", "48T15", "48U15", "48V15", "48W15", "48X15", 
"48AD15", "48AE15", "51A15", "51B15", "52A15", "56E15", "56F15", "56G15", 
"60A15", "60B15", "60C15", "60D15", "60E15", "60F15", "60G15", "60H15", "60I15",
"60J15", "60K15", "60L15", "60M15", "60N15", "60U15", "60V15", "60AA15", 
"60AB15", "60AC15", "60AD15", "63A15", "66A15", "67A15", "68A15", "68B15", 
"68C15", "68D15", "68E15", "68F15", "70A15", "70E15", "72F15", "72G15", "72H15",
"72I15", "72J15", "72K15", "80E15", "80F15", "80G15", "80H15", "80I15", "80J15",
"80K15", "80L15", "80N15", "80O15", "80Q15", "80R15", "80S15", "80T15", "80U15",
"80V15", "84A15", "84B15", "85A15", "85B15", "90A15", "90E15", "90G15", "90H15",
"90I15", "90J15", "93A15", "95A15", "96M15", "96N15", "96O15", "96S15", "98A15",
"99C15", "100A15", "102A15", "102B15", "102C15", "108A15", "110A15", "112A15", 
"112B15", "112C15", "112D15", "112E15", "112F15", "112G15", "112H15", "120A15", 
"120E15", "120F15", "120G15", "120H15", "120I15", "120J15", "120K15", "120L15", 
"124A15", "126A15", "126B15", "132A15", "132B15", "135A15", "135B15", "136A15", 
"136B15", "136C15", "136D15", "136E15", "136F15", "138A15", "138B15", "140A15", 
"140B15", "141A15", "144B15", "144C15", "144E15", "150I15", "150J15", "153A15", 
"154A15", "154B15", "155A15", "156A15", "156B15", "160A15", "160B15", "161A15", 
"165A15", "170A15", "170B15", "170C15", "170D15", "171A15", "174A15", "175A15", 
"177A15", "178A15", "178B15", "179A15", "182B15", "182C15", "193A15", "194A15", 
"194B15" ];

filtered[21] := [ Strings() | "16A21", "16B21", "16C21", "16D21", "16E21", 
"20B21", "20C21", "21A21", "21B21", "21C21", "22A21", "22B21", "22C21", "24A21",
"24B21", "24C21", "24D21", "24E21", "24F21", "24G21", "26A21", "28B21", "28C21",
"28D21", "28E21", "28I21", "28J21", "28M21", "30A21", "30B21", "30C21", "30D21",
"30G21", "30H21", "32A21", "32B21", "32C21", "32D21", "32E21", "32F21", "32G21",
"32H21", "32I21", "32J21", "32K21", "32N21", "32O21", "32Q21", "32R21", "33A21",
"33B21", "33C21", "34A21", "34B21", "35A21", "35B21", "36C21", "36E21", "36F21",
"39A21", "39B21", "40F21", "40H21", "40I21", "41A21", "42A21", "42B21", "42C21",
"42G21", "42H21", "44A21", "44B21", "44C21", "45A21", "45B21", "45C21", "45D21",
"45E21", "45F21", "48A21", "48B21", "48C21", "48D21", "48E21", "48F21", "48G21",
"48H21", "48I21", "48J21", "48K21", "48L21", "48M21", "48N21", "48O21", "48P21",
"48Q21", "48R21", "48S21", "48T21", "48U21", "48W21", "48X21", "48Y21", 
"48AB21", "48AC21", "48AD21", "48AE21", "48AF21", "48AH21", "48AI21", "48AJ21", 
"48AK21", "48AL21", "48AM21", "48AN21", "48AO21", "48AP21", "48AQ21", "48AR21", 
"48AS21", "48AT21", "48AY21", "48AZ21", "48BA21", "48BB21", "48BC21", "48BD21", 
"48BE21", "48BF21", "48BG21", "48BL21", "48BM21", "48BN21", "48BZ21", "48CA21", 
"48CB21", "48CC21", "48CD21", "48CE21", "48CF21", "48CG21", "48CH21", "48CI21", 
"48CJ21", "48CK21", "48CL21", "48CM21", "48CP21", "48CQ21", "50E21", "51A21", 
"52C21", "52D21", "54A21", "54B21", "55A21", "55B21", "56C21", "56D21", "56E21",
"56F21", "56G21", "56H21", "56L21", "56M21", "56N21", "60A21", "60B21", "60C21",
"60D21", "60S21", "60U21", "60V21", "60W21", "60X21", "63A21", "63C21", "64A21",
"64B21", "64C21", "64D21", "64E21", "64F21", "64G21", "64H21", "64J21", "64K21",
"64N21", "64O21", "64Q21", "65A21", "66B21", "66C21", "68C21", "69A21", "70A21",
"70G21", "70H21", "70I21", "72A21", "72B21", "72C21", "72D21", "72E21", "72F21",
"72G21", "72H21", "72I21", "72J21", "72K21", "72L21", "72AA21", "72AB21", 
"72AC21", "78A21", "78B21", "78C21", "80A21", "80B21", "80C21", "80D21", 
"80E21", "80F21", "80G21", "80H21", "80I21", "80J21", "80K21", "80L21", "80M21",
"80N21", "80O21", "80P21", "80Q21", "80S21", "80T21", "80U21", "80V21", "80W21",
"80X21", "80Y21", "80Z21", "80AA21", "80AB21", "84A21", "84B21", "84C21", 
"84D21", "84E21", "84F21", "84Q21", "88C21", "88D21", "88E21", "88F21", "88G21",
"88H21", "90A21", "90C21", "90D21", "90E21", "90F21", "90I21", "90N21", "90O21",
"91A21", "91B21", "92A21", "96A21", "96B21", "96C21", "96D21", "96E21", "96F21",
"96G21", "96H21", "96I21", "96J21", "96K21", "96L21", "96P21", "96Q21", "96R21",
"96S21", "96T21", "96U21", "96V21", "96W21", "96X21", "96AZ21", "96BA21", 
"96BB21", "96BC21", "96BD21", "96BE21", "96BF21", "96BG21", "96BH21", "96BI21", 
"96BJ21", "96BK21", "96BL21", "96BM21", "97A21", "99A21", "99B21", "100A21", 
"100B21", "102A21", "102B21", "102C21", "102D21", "104A21", "104B21", "104C21", 
"105B21", "105C21", "105D21", "105F21", "108E21", "110B21", "110C21", "111A21", 
"112E21", "112F21", "114A21", "115A21", "117A21", "117B21", "119A21", "120A21", 
"120B21", "120C21", "120D21", "120O21", "126J21", "126K21", "126L21", "126M21", 
"126N21", "126Q21", "126S21", "128A21", "128B21", "128C21", "128D21", "128E21", 
"128F21", "129A21", "130A21", "130B21", "130C21", "132B21", "132C21", "133B21", 
"135A21", "137A21", "138A21", "140B21", "140C21", "144A21", "144B21", "144C21", 
"144D21", "144E21", "144F21", "144G21", "144H21", "144I21", "144J21", "144K21", 
"144L21", "146A21", "147A21", "147B21", "150A21", "153A21", "154B21", "160A21", 
"160B21", "160C21", "160D21", "160E21", "160F21", "165B21", "168B21", "168C21", 
"170A21", "172A21", "176B21", "176C21", "178A21", "180A21", "180B21", "180C21", 
"180D21", "180I21", "184A21", "189B21", "189C21", "192A21", "192B21", "192C21", 
"192D21", "192M21", "192N21", "192O21", "192P21", "195A21", "196A21", "198B21", 
"198C21", "200A21", "200B21", "201A21", "207A21", "215A21", "216B21", "234A21", 
"245A21", "246A21", "246B21", "247A21", "249A21", "250A21", "251A21", "255A21", 
"256A21", "256B21", "257A21", "267A21" ];

// list of best value of M for the different groups

// This is the best M with normalizers, sorted by MK^2, which is the level at which we would have to work
grps_M := AssociativeArray();

grps_M[1] := [ car<IntegerRing(), Strings(), IntegerRing()> | <11, "11A1", 11>, 
<11, "11D1", 11>, <14, "14C1", 14>, <14, "14H1", 14>, <15, "15C1", 15>, <15, 
"15G1", 15>, <15, "15I1", 15>, <17, "17A1", 17>, <17, "17B1", 17>, <17, "17C1", 
17>, <19, "19A1", 19>, <19, "19B1", 19>, <20, "10A1", 5>, <20, "10D1", 5>, <20, 
"10G1", 5>, <21, "21B1", 21>, <21, "21F1", 21>, <27, "27A1", 27>, <27, "27C1", 
27>, <36, "18C1", 9>, <36, "18J1", 9>, <36, "6A1", 1>, <36, "6B1", 1>, <36, 
"6C1", 1>, <36, "6D1", 1>, <36, "6E1", 1>, <36, "6F1", 1>, <45, "15E1", 5>, <45,
"15H1", 5>, <49, "49A1", 49>, <49, "7A1", 1>, <49, "7B1", 1>, <49, "7C1", 1>, 
<50, "10B1", 2>, <50, "10F1", 2>, <50, "10I1", 2>, <52, "26A1", 13>, <52, 
"26B1", 13>, <64, "8A1", 1>, <64, "8B1", 1>, <64, "8C1", 1>, <64, "8F1", 1>, 
<64, "8G1", 1>, <64, "8I1", 1>, <64, "8K1", 1>, <75, "15B1", 3>, <81, "9A1", 1>,
<81, "9C1", 1>, <81, "9D1", 1>, <81, "9E1", 1>, <81, "9G1", 1>, <81, "9H1", 1>, 
<100, "10C1", 1>, <100, "10E1", 1>, <100, "10H1", 1>, <100, "10K1", 1>, <121, 
"11B1", 1>, <121, "11C1", 1>, <144, "12B1", 1>, <144, "12C1", 1>, <144, "12F1", 
1>, <144, "12J1", 1>, <144, "12K1", 1>, <144, "12L1", 1>, <144, "12M1", 1>, 
<144, "12P1", 1>, <144, "12S1", 1>, <144, "12T1", 1>, <144, "12V1", 1>, <162, 
"18E1", 2>, <162, "18I1", 2>, <180, "30C1", 5>, <180, "30D1", 5>, <196, "14E1", 
1>, <196, "14G1", 1>, <225, "15A1", 1>, <225, "15D1", 1>, <225, "15F1", 1>, 
<256, "16A1", 1>, <256, "16B1", 1>, <256, "16C1", 1>, <256, "16D1", 1>, <256, 
"16E1", 1>, <256, "16F1", 1>, <256, "16G1", 1>, <256, "16H1", 1>, <256, "16I1", 
1>, <256, "16J1", 1>, <256, "16M1", 1>, <324, "18A1", 1>, <324, "18F1", 1>, 
<324, "18G1", 1>, <324, "18H1", 1>, <400, "20D1", 1>, <400, "20E1", 1>, <400, 
"20H1", 1>, <400, "20I1", 1>, <441, "21E1", 1>, <576, "24C1", 1>, <576, "24D1", 
1>, <576, "24E1", 1>, <576, "24G1", 1>, <576, "24H1", 1>, <576, "24J1", 1>, 
<729, "27B1", 1>, <1024, "32A1", 1>, <1024, "32E1", 1>, <1296, "36C1", 1> ];

// Errors
// 18E1, 18I1 - assertion Dimension(H) eq 1 failed!
// 16A1-16M1 - field embeddings fail to commute!
// 24C1 - field embeddings fail to commute!

grps_M[3] := [ car<IntegerRing(), Strings(), IntegerRing()> | <20, "20S3", 20>, 
<21, "21D3", 21>, <24, "24X3", 24>, <24, "24Y3", 24>, <30, "30K3", 30>, <33, 
"33C3", 33>, <34, "34C3", 34>, <35, "35A3", 35>, <36, "18G3", 9>, <36, "18I3", 
9>, <36, "36K3", 36>, <39, "39A3", 39>, <41, "41A3", 41>, <43, "43A3", 43>, <45,
"15E3", 5>, <45, "15F3", 5>, <45, "45D3", 45>, <48, "12K3", 3>, <49, "49A3", 
49>, <49, "7A3", 1>, <52, "26A3", 13>, <60, "30F3", 15>, <60, "30G3", 15>, <63, 
"21A3", 7>, <64, "8A3", 1>, <64, "8B3", 1>, <68, "34A3", 17>, <68, "34B3", 17>, 
<75, "15A3", 3>, <75, "15G3", 3>, <80, "20A3", 5>, <80, "20I3", 5>, <80, "20J3",
5>, <80, "20K3", 5>, <80, "20L3", 5>, <81, "9A3", 1>, <84, "42D3", 21>, <84, 
"42E3", 21>, <98, "14D3", 2>, <99, "33A3", 11>, <100, "10A3", 1>, <100, "10B3", 
1>, <100, "10C3", 1>, <100, "50A3", 25>, <144, "12A3", 1>, <144, "12D3", 1>, 
<144, "12E3", 1>, <144, "12F3", 1>, <144, "12G3", 1>, <144, "12I3", 1>, <144, 
"12J3", 1>, <144, "12L3", 1>, <144, "12N3", 1>, <144, "12O3", 1>, <144, "12P3", 
1>, <144, "36A3", 9>, <153, "51A3", 17>, <162, "18J3", 2>, <169, "13A3", 1>, 
<169, "13B3", 1>, <169, "13C3", 1>, <180, "30B3", 5>, <180, "30I3", 5>, <180, 
"30J3", 5>, <192, "24C3", 3>, <196, "14A3", 1>, <196, "14C3", 1>, <208, "52B3", 
13>, <225, "15B3", 1>, <225, "15C3", 1>, <225, "15H3", 1>, <256, "16A3", 1>, 
<256, "16B3", 1>, <256, "16C3", 1>, <256, "16D3", 1>, <256, "16E3", 1>, <256, 
"16F3", 1>, <256, "16H3", 1>, <256, "16I3", 1>, <256, "16J3", 1>, <256, "16K3", 
1>, <256, "16L3", 1>, <256, "16N3", 1>, <256, "16O3", 1>, <256, "16R3", 1>, 
<256, "16S3", 1>, <320, "40C3", 5>, <320, "40D3", 5>, <320, "40G3", 5>, <320, 
"40H3", 5>, <320, "40J3", 5>, <324, "18A3", 1>, <324, "18D3", 1>, <324, "18F3", 
1>, <324, "18H3", 1>, <324, "18K3", 1>, <400, "20E3", 1>, <400, "20F3", 1>, 
<400, "20G3", 1>, <400, "20H3", 1>, <400, "20P3", 1>, <400, "20R3", 1>, <400, 
"20T3", 1>, <441, "21C3", 1>, <450, "30D3", 2>, <576, "24A3", 1>, <576, "24AA3",
1>, <576, "24AC3", 1>, <576, "24B3", 1>, <576, "24H3", 1>, <576, "24I3", 1>, 
<576, "24K3", 1>, <576, "24L3", 1>, <576, "24N3", 1>, <576, "24O3", 1>, <576, 
"24P3", 1>, <576, "24Q3", 1>, <576, "24U3", 1>, <576, "24V3", 1>, <576, "24W3", 
1>, <576, "24Z3", 1>, <576, "72A3", 9>, <729, "27A3", 1>, <729, "27C3", 1>, 
<784, "28C3", 1>, <900, "30A3", 1>, <900, "30H3", 1>, <1024, "32A3", 1>, <1024, 
"32B3", 1>, <1024, "32C3", 1>, <1024, "32J3", 1>, <1024, "32K3", 1>, <1024, 
"32L3", 1>, <1024, "32M3", 1>, <1024, "32N3", 1>, <1024, "32O3", 1>, <1024, 
"32P3", 1>, <1296, "36D3", 1>, <1296, "36E3", 1>, <1296, "36G3", 1>, <1296, 
"36I3", 1>, <1296, "36J3", 1>, <1600, "40E3", 1>, <1600, "40F3", 1>, <2025, 
"45A3", 1>, <2025, "45B3", 1>, <2304, "48C3", 1>, <2304, "48D3", 1>, <2304, 
"48E3", 1>, <2304, "48F3", 1>, <2304, "48G3", 1>, <2304, "48H3", 1>, <2304, 
"48I3", 1>, <2304, "48J3", 1>, <2304, "48K3", 1>, <2304, "48L3", 1>, <2304, 
"48M3", 1>, <2916, "54A3", 1>, <4096, "64A3", 1>, <4096, "64B3", 1> ];

// Errors
// 20S3, 24X3 - assertion Dimension(H) eq 1 failed!

grps_M[6] := [ car<IntegerRing(), Strings(), IntegerRing()> | <22, "22C6", 22>, 
<31, "31A6", 31>, <31, "31B6", 31>, <44, "22A6", 11>, <58, "58A6", 58>, <71, 
"71A6", 71>, <79, "79A6", 79>, <90, "30C6", 10>, <100, "10A6", 1>, <112, "28D6",
7>, <112, "28E6", 7>, <112, "28G6", 7>, <117, "39A6", 13>, <121, "11A6", 1>, 
<121, "121A6", 121>, <147, "21B6", 3>, <162, "18A6", 2>, <172, "86A6", 43>, 
<196, "14B6", 1>, <207, "69A6", 23>, <245, "35E6", 5>, <261, "87A6", 29>, <289, 
"17A6", 1>, <300, "30E6", 3>, <324, "18B6", 1>, <324, "18C6", 1>, <396, "66B6", 
11>, <396, "66D6", 11>, <400, "20C6", 1>, <400, "20D6", 1>, <405, "45D6", 5>, 
<441, "21C6", 1>, <448, "56D6", 7>, <448, "56E6", 7>, <450, "30A6", 2>, <468, 
"78A6", 13>, <484, "22B6", 1>, <567, "63A6", 7>, <576, "24D6", 1>, <576, "24G6",
1>, <729, "27A6", 1>, <768, "48D6", 3>, <784, "28I6", 1>, <900, "30B6", 1>, 
<900, "30D6", 1>, <1024, "32A6", 1>, <1024, "32B6", 1>, <1296, "36C6", 1>, 
<1296, "36D6", 1>, <1296, "36E6", 1>, <1296, "36F6", 1>, <1296, "36J6", 1>, 
<1296, "36K6", 1>, <1620, "90B6", 5>, <2025, "45A6", 1>, <2025, "45C6", 1>, 
<2304, "48A6", 1>, <2304, "48B6", 1>, <2304, "48C6", 1>, <2304, "48I6", 1>, 
<2304, "48J6", 1>, <2500, "50E6", 1>, <2704, "52A6", 1>, <2916, "54A6", 1>, 
<2916, "54B6", 1>, <3600, "60B6", 1>, <3600, "60C6", 1>, <3600, "60E6", 1>, 
<3600, "60F6", 1>, <5184, "72B6", 1>, <5184, "72C6", 1>, <5184, "72D6", 1>, 
<8100, "90C6", 1>, <10000, "100A6", 1> ];

grps_M[10] := [ car<IntegerRing(), Strings(), IntegerRing()> | <26, "26D10", 
26>, <28, "28D10", 28>, <37, "37A10", 37>, <38, "38A10", 38>, <54, "54I10", 54>,
<81, "81A10", 81>, <81, "9A10", 1>, <86, "86A10", 86>, <108, "54B10", 27>, <108,
"54E10", 27>, <117, "39B10", 13>, <127, "127A10", 127>, <148, "74A10", 37>, 
<150, "30F10", 6>, <162, "18L10", 2>, <176, "44B10", 11>, <176, "44C10", 11>, 
<225, "15A10", 1>, <225, "15B10", 1>, <225, "45B10", 9>, <225, "75A10", 25>, 
<236, "118A10", 59>, <242, "22A10", 2>, <252, "42D10", 7>, <252, "42E10", 7>, 
<252, "42G10", 7>, <252, "42H10", 7>, <268, "134A10", 67>, <304, "76A10", 19>, 
<324, "18A10", 1>, <324, "18B10", 1>, <324, "18C10", 1>, <324, "18D10", 1>, 
<324, "18E10", 1>, <324, "18F10", 1>, <324, "18G10", 1>, <324, "18H10", 1>, 
<324, "18M10", 1>, <400, "20A10", 1>, <400, "20B10", 1>, <400, "20C10", 1>, 
<400, "20D10", 1>, <400, "20E10", 1>, <400, "20F10", 1>, <405, "45A10", 5>, 
<432, "108A10", 27>, <441, "21A10", 1>, <450, "30H10", 2>, <468, "78A10", 13>, 
<575, "115A10", 23>, <576, "24A10", 1>, <576, "24B10", 1>, <625, "25A10", 1>, 
<676, "26A10", 1>, <676, "26E10", 1>, <684, "114A10", 19>, <684, "114B10", 19>, 
<704, "88C10", 11>, <729, "27B10", 1>, <784, "28C10", 1>, <810, "90E10", 10>, 
<882, "42K10", 2>, <900, "150A10", 25>, <900, "30A10", 1>, <900, "30B10", 1>, 
<900, "30C10", 1>, <1024, "32B10", 1>, <1089, "33B10", 1>, <1089, "33C10", 1>, 
<1100, "110A10", 11>, <1296, "36A10", 1>, <1296, "36B10", 1>, <1296, "36C10", 
1>, <1296, "36G10", 1>, <1296, "36I10", 1>, <1296, "36J10", 1>, <1296, "36K10", 
1>, <1296, "36M10", 1>, <1296, "36N10", 1>, <1296, "36O10", 1>, <1296, "36Q10", 
1>, <1296, "36R10", 1>, <1296, "36S10", 1>, <1575, "105A10", 7>, <1600, "40C10",
1>, <1600, "40D10", 1>, <1600, "40E10", 1>, <1600, "40F10", 1>, <1600, "40G10", 
1>, <1764, "42A10", 1>, <1764, "42I10", 1>, <2116, "46A10", 1>, <2304, "48A10", 
1>, <2304, "48B10", 1>, <2304, "48C10", 1>, <2304, "48D10", 1>, <2500, "50A10", 
1>, <2704, "52A10", 1>, <2916, "54A10", 1>, <2916, "54C10", 1>, <2916, "54G10", 
1>, <3136, "56F10", 1>, <3600, "60C10", 1>, <4050, "90D10", 2>, <5184, "72A10", 
1>, <5184, "72B10", 1>, <5184, "72C10", 1>, <5184, "72D10", 1>, <6400, "80A10", 
1>, <6400, "80B10", 1>, <7056, "84B10", 1>, <7056, "84C10", 1>, <7744, "88B10", 
1>, <8100, "90A10", 1>, <8100, "90F10", 1>, <8464, "92A10", 1>, <9216, "96A10", 
1>, <9216, "96B10", 1>, <10000, "100A10", 1>, <11664, "108F10", 1> ];

grps_M[15] := [ car<IntegerRing(), Strings(), IntegerRing()> | <43, "43A15", 
43>, <60, "60AC15", 60>, <60, "60AD15", 60>, <67, "67A15", 67>, <85, "85A15", 
85>, <85, "85B15", 85>, <102, "102C15", 102>, <110, "110A15", 110>, <141, 
"141A15", 141>, <153, "153A15", 153>, <153, "51A15", 17>, <153, "51B15", 17>, 
<155, "155A15", 155>, <161, "161A15", 161>, <175, "175A15", 175>, <175, "35B15",
7>, <175, "35C15", 7>, <179, "179A15", 179>, <193, "193A15", 193>, <196, 
"14A15", 1>, <196, "98A15", 49>, <198, "66A15", 22>, <200, "40L15", 8>, <200, 
"40M15", 8>, <208, "52A15", 13>, <245, "35D15", 5>, <272, "68A15", 17>, <272, 
"68E15", 17>, <272, "68F15", 17>, <276, "138A15", 69>, <276, "138B15", 69>, 
<279, "93A15", 31>, <289, "17A15", 1>, <300, "150I15", 75>, <300, "150J15", 75>,
<300, "30B15", 3>, <300, "30C15", 3>, <308, "154A15", 77>, <308, "154B15", 77>, 
<320, "40AE15", 5>, <320, "40AF15", 5>, <338, "26A15", 2>, <340, "170C15", 85>, 
<340, "170D15", 85>, <356, "178A15", 89>, <356, "178B15", 89>, <364, "182B15", 
91>, <364, "182C15", 91>, <388, "194A15", 97>, <388, "194B15", 97>, <400, 
"100A15", 25>, <400, "20A15", 1>, <400, "20D15", 1>, <400, "20E15", 1>, <400, 
"20G15", 1>, <405, "45A15", 5>, <405, "45B15", 5>, <441, "21A15", 1>, <441, 
"21B15", 1>, <450, "30F15", 2>, <475, "95A15", 19>, <528, "132A15", 33>, <528, 
"132B15", 33>, <529, "23A15", 1>, <531, "177A15", 59>, <560, "140A15", 35>, 
<560, "140B15", 35>, <576, "24A15", 1>, <576, "24B15", 1>, <576, "24D15", 1>, 
<576, "24E15", 1>, <576, "24F15", 1>, <576, "24G15", 1>, <576, "24H15", 1>, 
<576, "24I15", 1>, <576, "24J15", 1>, <576, "24M15", 1>, <576, "24N15", 1>, 
<576, "24Q15", 1>, <576, "24R15", 1>, <588, "42A15", 3>, <588, "42B15", 3>, 
<612, "102A15", 17>, <612, "102B15", 17>, <624, "156A15", 39>, <624, "156B15", 
39>, <720, "60C15", 5>, <720, "60D15", 5>, <720, "60L15", 5>, <720, "60N15", 5>,
<784, "28C15", 1>, <784, "28D15", 1>, <784, "28E15", 1>, <784, "28F15", 1>, 
<882, "42D15", 2>, <891, "99C15", 11>, <900, "30A15", 1>, <900, "30E15", 1>, 
<980, "70E15", 5>, <1008, "84A15", 7>, <1008, "84B15", 7>, <1044, "174A15", 29>,
<1088, "136B15", 17>, <1088, "136E15", 17>, <1088, "136F15", 17>, <1156, 
"34A15", 1>, <1225, "35A15", 1>, <1280, "80U15", 5>, <1296, "36A15", 1>, <1296, 
"36B15", 1>, <1296, "36C15", 1>, <1296, "36D15", 1>, <1521, "39A15", 1>, <1539, 
"171A15", 19>, <1600, "40AA15", 1>, <1600, "40AB15", 1>, <1600, "40AD15", 1>, 
<1600, "40B15", 1>, <1600, "40C15", 1>, <1600, "40D15", 1>, <1600, "40E15", 1>, 
<1600, "40F15", 1>, <1600, "40G15", 1>, <1600, "40H15", 1>, <1600, "40I15", 1>, 
<1600, "40N15", 1>, <1600, "40O15", 1>, <1600, "40R15", 1>, <1600, "40S15", 1>, 
<1600, "40U15", 1>, <1600, "40V15", 1>, <1600, "40W15", 1>, <1600, "40X15", 1>, 
<1600, "40Y15", 1>, <1600, "40Z15", 1>, <1620, "90I15", 5>, <1620, "90J15", 5>, 
<1700, "170A15", 17>, <1700, "170B15", 17>, <1764, "42C15", 1>, <1792, "112C15",
7>, <1792, "112E15", 7>, <1792, "112F15", 7>, <2025, "45D15", 1>, <2304, 
"144E15", 9>, <2304, "48AD15", 1>, <2304, "48AE15", 1>, <2304, "48E15", 1>, 
<2304, "48F15", 1>, <2304, "48G15", 1>, <2304, "48H15", 1>, <2304, "48I15", 1>, 
<2304, "48K15", 1>, <2304, "48L15", 1>, <2304, "48M15", 1>, <2304, "48N15", 1>, 
<2304, "48O15", 1>, <2304, "48P15", 1>, <2304, "48Q15", 1>, <2304, "48R15", 1>, 
<2304, "48T15", 1>, <2304, "48U15", 1>, <2304, "48V15", 1>, <2304, "48W15", 1>, 
<2304, "48X15", 1>, <2475, "165A15", 11>, <2880, "120H15", 5>, <3136, "56E15", 
1>, <3136, "56F15", 1>, <3136, "56G15", 1>, <3600, "60A15", 1>, <3600, "60AA15",
1>, <3600, "60AB15", 1>, <3600, "60B15", 1>, <3600, "60E15", 1>, <3600, "60F15",
1>, <3600, "60G15", 1>, <3600, "60H15", 1>, <3600, "60I15", 1>, <3600, "60J15", 
1>, <3600, "60K15", 1>, <3600, "60M15", 1>, <3600, "60U15", 1>, <3600, "60V15", 
1>, <3969, "63A15", 1>, <4624, "68B15", 1>, <4624, "68C15", 1>, <4624, "68D15", 
1>, <4900, "70A15", 1>, <5184, "72F15", 1>, <5184, "72G15", 1>, <5184, "72H15", 
1>, <5184, "72I15", 1>, <5184, "72J15", 1>, <5184, "72K15", 1>, <6400, "80E15", 
1>, <6400, "80F15", 1>, <6400, "80G15", 1>, <6400, "80H15", 1>, <6400, "80I15", 
1>, <6400, "80J15", 1>, <6400, "80K15", 1>, <6400, "80L15", 1>, <6400, "80N15", 
1>, <6400, "80O15", 1>, <6400, "80Q15", 1>, <6400, "80R15", 1>, <6400, "80S15", 
1>, <6400, "80T15", 1>, <6400, "80V15", 1>, <8100, "90A15", 1>, <8100, "90E15", 
1>, <8100, "90G15", 1>, <8100, "90H15", 1>, <9216, "96M15", 1>, <9216, "96N15", 
1>, <9216, "96O15", 1>, <9216, "96S15", 1>, <11664, "108A15", 1>, <12544, 
"112A15", 1>, <12544, "112B15", 1>, <12544, "112D15", 1>, <12544, "112G15", 1>, 
<12544, "112H15", 1>, <14400, "120A15", 1>, <14400, "120E15", 1>, <14400, 
"120F15", 1>, <14400, "120G15", 1>, <14400, "120I15", 1>, <14400, "120J15", 1>, 
<14400, "120K15", 1>, <14400, "120L15", 1>, <15376, "124A15", 1>, <15876, 
"126A15", 1>, <15876, "126B15", 1>, <18225, "135A15", 1>, <18225, "135B15", 1>, 
<18496, "136A15", 1>, <18496, "136C15", 1>, <18496, "136D15", 1>, <20736, 
"144B15", 1>, <20736, "144C15", 1>, <25600, "160A15", 1>, <25600, "160B15", 1> 
];

/*
grps_M := [ <"11A6", 1>, <"14B6", 1>, <"17A6", 1>, <"18A6", 1>, <"18B6", 1>, <"18C6", 1>, <"20C6", 1>, <"21B6", 3>, <"21C6", 1>, <"22A6", 1>, <"22B6", 1>, <"22C6", 1>, <"24D6", 1>, <"24G6", 1>, <"27A6", 1>, <"28D6", 1>, <"28E6", 1>, <"28G6", 1>, <"28I6", 1>, <"30A6", 2>, <"30B6", 1>, <"30C6", 1>, <"30D6", 1>, <"30E6", 3>, <"31A6", 1>, <"31B6", 1>, <"32A6", 1>, <"32B6", 1>, <"35E6", 5>, <"36C6", 1>, <"36D6", 1>, <"36E6", 1>, <"36F6", 1>, <"36J6", 1>, <"36K6", 1>, <"39A6", 1>, <"45A6", 1>, <"45C6", 1>, <"45D6", 1>, <"48A6", 1>, <"48B6", 1>, <"48C6", 1>, <"48D6", 1>, <"48I6", 1>, <"48J6", 1>, <"50E6", 1>, <"52A6", 1>, <"54A6", 1>, <"54B6", 1>, <"56D6", 1>, <"56E6", 1>, <"58A6", 58>, <"60B6", 1>, <"60C6", 1>, <"60E6", 1>, <"60F6", 1>, <"63A6", 7>, <"66B6", 11>, <"66D6", 11>, <"69A6", 23>, <"71A6", 71>, <"72B6", 1>, <"72C6", 1>, <"72D6", 1>, <"78A6", 1>, <"79A6", 79>, <"86A6", 43>, <"87A6", 29>, <"90B6", 1>, <"90C6", 1>, <"100A6", 1>, <"121A6", 121> ];
*/


SetDebugOnError(true);
SetVerbose("ModularCurves", 1);

procedure computeShimuraModularCurves(shim, grps : Proof := false)

    //    for g in [1,3,6,10,15] do
    for g in genera do
	for name in shim[g] do
	    X, fs := qExpansionBasisShimura(name, grps : Proof := Proof);
	    write_qexps(name cat "_shim", fs, X);
	    print "Group ", name, " - done!";
	end for;
    end for;
    
end procedure;

function FindEquationsGenus(genus)
    errors := [];
// for genus in [1,3,6,10] do
    check := genus lt 10;
    for grp in grps_M[genus] do
	try
	    testBoxSingle(grps, grp[2] : Proof, Normalizers, WriteFile, CheckGenus := check);
	catch e
	    Append(~errors, <grp[2], e`Object>);
	    try
		testBoxSingle(grps, grp[2] : Proof, WriteFile, CheckGenus := check);
	    catch err
		Append(~errors, <grp[2], err`Object>);
	    end try;
	end try;
    end for;
    //end for;
    return errors;
end function;