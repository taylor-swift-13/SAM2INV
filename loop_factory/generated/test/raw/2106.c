int main1(){
  int mv, dn, bf, bl0, ijm;

  mv=1+21;
  dn=0;
  bf=bl0;
  bl0=dn;
  ijm=dn;

  while (dn < mv) {
      dn = dn + 1;
      bf = bf < ijm ? bf : ijm;
      ijm = ijm + mv;
  }

}
