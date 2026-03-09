int main1(int i,int c){
  int to4, r66n, a9;
  to4=i+14;
  r66n=0;
  a9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant to4 == \at(i, Pre) + 14;
  loop invariant r66n == 2*(c - \at(c, Pre));
  loop invariant i == \at(i, Pre) + (c - \at(c, Pre)) * ((c - \at(c, Pre)) + 1);
  loop invariant c >= \at(c, Pre);
  loop invariant 2*a9 == 5*r66n;
  loop assigns r66n, a9, i, c;
*/
while (r66n<to4) {
      r66n += 2;
      a9 = a9 + 5;
      i += r66n;
      c = c + 1;
  }
}