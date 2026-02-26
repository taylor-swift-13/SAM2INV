int main1(int m,int p){
  int n, v, c;

  n=49;
  v=0;
  c=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 49;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v >= 0;
  loop invariant (v == 0) ==> (c == -2);
  loop invariant v >= 0 && (c == -2 || c == 1);
  loop invariant (m == \at(m, Pre)) && (p == \at(p, Pre)) && (v >= 0) && ((c == -2) || (c == 1));
  loop invariant (c == -2) || (c == 1);
  loop invariant ((v == 0 && c == -2) || (v >= 1 && c == 1)) && n == 49 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant c <= 1;
  loop assigns c, v;
*/
while (1) {
      if (n<c+4) {
          c = c+c;
      }
      c = c-c;
      c = c+1;
      v = v+1;
  }

}
