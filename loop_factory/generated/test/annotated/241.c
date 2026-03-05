int main1(int j,int h){
  int ocgv, t3e;
  ocgv=(j%19)+13;
  t3e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ocgv == \at(j, Pre) % 19 + 13;
  loop invariant h == \at(h, Pre) + t3e * ocgv;
  loop invariant h == \at(h, Pre) + t3e * ocgv && 0 <= t3e && (ocgv <= 0 || t3e <= ocgv);
  loop invariant j == \at(j, Pre);
  loop assigns t3e, h;
*/
while (t3e<ocgv) {
      t3e++;
      if (t3e<=t3e) {
          t3e = t3e;
      }
      h = h + ocgv;
  }
}