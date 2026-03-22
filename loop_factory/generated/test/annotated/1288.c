int main1(){
  int p, pz, y0, hp, kf;
  p=40;
  pz=p;
  y0=p;
  hp=p;
  kf=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 40;
  loop invariant 40 <= y0 <= 70;
  loop invariant y0 == kf;
  loop invariant 5*(p - pz) == 6*(y0 - p);
  loop invariant pz + 2*hp == 120;
  loop invariant pz + 3*(kf - hp) == 40;
  loop assigns y0, hp, kf, pz;
*/
while (1) {
      if (!(pz>=6)) {
          break;
      }
      y0 = y0 + 5;
      hp = hp + 3;
      kf = kf + 5;
      pz -= 6;
  }
}