int main1(int x){
  int dm, d, r5e, zh;
  dm=x+8;
  d=dm;
  r5e=0;
  zh=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zh == 5 + d * r5e;
  loop invariant d == dm;
  loop invariant dm == \at(x, Pre) + 8;
  loop invariant r5e >= 0;
  loop assigns r5e, x, zh;
*/
while (r5e<=dm-1) {
      zh += d;
      r5e++;
      x += r5e;
  }
}