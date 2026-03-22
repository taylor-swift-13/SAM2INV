int main1(){
  int i45w, qs, c, yhb, hm, qvz;
  i45w=1+15;
  qs=i45w;
  c=0;
  yhb=qs;
  hm=0;
  qvz=i45w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yhb == i45w - c;
  loop invariant c <= i45w;
  loop invariant hm == c * qs;
  loop invariant 0 <= c;
  loop invariant 0 <= hm;
  loop invariant qs == i45w;
  loop assigns c, hm, yhb;
*/
while (c<i45w) {
      c = c + 1;
      hm += qs;
      yhb = i45w-c;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c - (hm*hm - 2*hm) == -65008;
  loop invariant qs > 0;
  loop invariant c >= 0;
  loop invariant hm >= 0;
  loop invariant qs - qvz * hm <= 0;
  loop invariant i45w >= 0;
  loop assigns c, hm, qs;
*/
while (hm<=yhb) {
      c = c+2*hm-1;
      hm = hm + 1;
      qs = qs + qvz;
  }
}