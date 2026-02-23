int main1(int p,int q){
  int m, c, w;

  m=33;
  c=1;
  w=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 33;
  loop invariant (1 <= c);
  loop invariant (c <= m);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (c == 1) ==> (w == 1) && (c != 1) ==> (w == 0);
  loop invariant (c == 1) ==> (w == 1);
  loop invariant c <= m;
  loop invariant 1 <= c;
  loop invariant (m == 33);
  loop invariant (1 <= c && c <= m);
  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant ((c == 1) ==> (w == 1));
  loop assigns w, c;
*/
while (c<m) {
      w = w+w;
      w = w-w;
      c = c+1;
  }

}
