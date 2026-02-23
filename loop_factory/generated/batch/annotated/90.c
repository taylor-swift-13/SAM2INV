int main1(int b,int n){
  int i, v, c;

  i=11;
  v=i;
  c=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (i < b + 4) ==> c + v == 5;
  loop invariant (i >= b + 4) ==> c == -6;
  loop invariant 0 <= v && v <= 11;
  loop invariant i == 11;
  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (i < b + 4) ==> c == -6 + (11 - v);
  loop invariant (b == \at(b, Pre));
  loop invariant (n == \at(n, Pre));
  loop invariant (0 <= v) && (v <= 11);
  loop invariant (-6 <= c) && (c <= 5);
  loop invariant (b > 7) ==> c == -6 + (11 - v);
  loop invariant v <= 11;
  loop invariant 0 <= v;
  loop invariant -6 <= c + v;
  loop invariant c + v <= 5;
  loop assigns c, v;
*/
while (v>0) {
      if (i<b+4) {
          c = c+1;
      }
      v = v-1;
  }

}
