int main1(int k,int n){
  int f, j, v, o;

  f=20;
  j=f;
  v=f;
  o=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 20;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 20 <= v;
  loop invariant v <= 21;
  loop invariant o >= -4;
  loop invariant j == 20;
  loop invariant ((o + 4) % 21) == 0;
  loop invariant f <= v;
  loop invariant v <= f + 1;
  loop invariant ((o + 4) % 21 == 0) &&
                   (j == 20) &&
                   (f == 20) &&
                   (k == \at(k, Pre)) &&
                   (n == \at(n, Pre));
  loop invariant (((v == 20) || (v == 21)) && (o >= -4));
  loop invariant v >= 20;
  loop assigns v, o;
*/
while (j-1>=0) {
      if (v+1<=f) {
          v = v+1;
      }
      else {
          v = f;
      }
      v = v+1;
      o = o+v;
  }

}
