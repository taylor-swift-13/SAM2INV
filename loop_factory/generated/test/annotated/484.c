int main1(){
  int niw, sg, vf, ikc, u0, fkd2, gk;
  niw=1+14;
  sg=0;
  vf=0;
  ikc=0;
  u0=0;
  fkd2=(1%18)+5;
  gk=sg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (fkd2 + ikc == 6);
  loop invariant (u0 == vf);
  loop invariant vf == ikc;
  loop invariant niw == 15;
  loop invariant fkd2 >= 0;
  loop invariant ikc >= 0;
  loop invariant gk >= 2*ikc;
  loop assigns u0, vf, fkd2, ikc, gk;
*/
while (fkd2>0) {
      u0 = u0+1*1;
      vf = vf+1*1;
      fkd2 = fkd2 - 1;
      ikc = ikc+1*1;
      gk = gk*2+(ikc%2)+2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (niw % 5 == 0);
  loop invariant niw >= 15;
  loop invariant sg == 0;
  loop assigns niw;
*/
for (; niw<=sg-5; niw = niw + 5) {
  }
}