int main1(){
  int kha, s, bhb, pn9h, f, h9;
  kha=1-7;
  s=0;
  bhb=5;
  pn9h=-4;
  f=s;
  h9=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0;
  loop invariant bhb - pn9h == 9;
  loop invariant kha == 1 - 7;
  loop invariant h9 * 2 == (pn9h + 4) * (pn9h - 3);
  loop assigns bhb, f, h9, pn9h;
*/
while (pn9h<kha) {
      pn9h += 1;
      bhb = bhb + 1;
      h9 = h9 + pn9h;
      f = f*2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f <= s;
  loop invariant s == 0;
  loop assigns kha, bhb, pn9h, f;
*/
while (1) {
      kha = kha + pn9h;
      bhb += kha;
      pn9h += 1;
      f = f + 1;
      if (f>=s) {
          break;
      }
  }
}