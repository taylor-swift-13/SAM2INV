int main1(int m,int q){
  int x, c, o, v, l, p;

  x=m+14;
  c=0;
  o=-3;
  v=x;
  l=c;
  p=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == -3;
  loop invariant c >= 0;

  loop invariant x == m + 14;
  loop invariant m == \at(m, Pre);

  loop invariant q == \at(q, Pre);
  loop invariant x == \at(m, Pre) + 14;
  loop invariant (c == 0) ==> (p == 6);


  loop invariant 0 <= c && (c == 0 || c <= x);
  loop invariant o == o % 6;
  loop assigns p, o, c;
*/
while (c<x) {
      p = p*p+o;
      o = o%6;
      c = c+1;
  }

}
