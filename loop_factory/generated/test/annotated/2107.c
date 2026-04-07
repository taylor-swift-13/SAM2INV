int main1(){
  int mv, dn, bf, bl0, ijm;
  mv=1+21;
  dn=0;
  bf=bl0;
  bl0=dn;
  ijm=dn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ijm == mv * dn;
  loop invariant mv == 22;
  loop invariant dn == 0 || bf <= ijm;
  loop invariant (0 <= dn && dn <= mv);
  loop assigns dn, bf, ijm;
*/
while (dn < mv) {
      dn = dn + 1;
      bf = bf < ijm ? bf : ijm;
      ijm = ijm + mv;
  }
}