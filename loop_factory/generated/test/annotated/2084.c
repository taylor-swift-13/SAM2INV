int main1(int e){
  int buhz, nc, t, sv;
  buhz=e+7;
  nc=0;
  t=0;
  sv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sv == (e * nc);
  loop invariant t == ((e * nc * (nc + 1)) / 2);
  loop invariant buhz == \at(e, Pre) + 7;
  loop invariant e == \at(e, Pre);
  loop invariant (nc >= 0);
  loop invariant (buhz <= 0) || (nc <= buhz);
  loop assigns nc, sv, t;
*/
while (1) {
      if (!(nc < buhz)) {
          break;
      }
      nc += 1;
      sv = sv + e;
      t = t + sv;
  }
}