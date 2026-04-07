int main1(int l){
  int a0f, u66, gc0, kdi;
  a0f=(l%8)+20;
  u66=0;
  gc0=a0f;
  kdi=a0f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u66 % 2 == 0;
  loop invariant gc0 - a0f - u66 == (u66/2) * (u66/2);
  loop invariant kdi <= a0f;
  loop invariant 0 <= u66;
  loop invariant 0 <= kdi;
  loop invariant 13 <= a0f;
  loop assigns u66, kdi, gc0;
*/
while (u66<=a0f-1) {
      u66 += 2;
      if (!(!(u66<=kdi))) {
          kdi = u66;
      }
      gc0 = gc0 + u66;
      gc0++;
  }
}