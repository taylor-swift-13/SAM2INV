int main1(int b,int n){
  int i, v, c, e;

  i=11;
  v=i;
  c=-6;
  e=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c + v == 5 && v >= 0 && c >= -6;
  loop invariant v >= 0;
  loop invariant v <= 11;
  loop invariant c + v == 5;
  loop invariant i == 11;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (-6 <= c) && (c <= 5);
  loop invariant (0 <= v) && (v <= 11);
  loop invariant v <= i;
  loop invariant 0 <= v;
  loop invariant c == i - v - 6;
  loop assigns c, v;
*/
while (v>0) {
      c = c+1;
      v = v-1;
  }

}
