int main1(int e,int l){
  int e1, j, be;
  e1=l;
  j=e1+3;
  be=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(e, Pre);
  loop invariant e1 == \at(l, Pre);
  loop invariant j == e1 + 3;
  loop invariant be >= -5;
  loop assigns be, l;
*/
while (j>0) {
      be++;
      be = be+be*be;
      l = l*4+(be%2)+3;
  }
}