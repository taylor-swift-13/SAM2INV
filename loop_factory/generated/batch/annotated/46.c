int main1(int p,int q){
  int m, c, w;

  m=33;
  c=m;
  w=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 33;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= c && c <= 33;
  loop invariant 0 <= w && w <= 33;
  loop invariant c >= 0;
  loop invariant w >= 0;
  loop invariant w <= c + 1;
  loop invariant (c == 33 && w == 6) || (w == c + 1);
  loop invariant c <= m;
  loop invariant ((c == 33 && w == 6) || w == c + 1);
  loop invariant 0 <= c;
  loop invariant c <= 33;
  loop invariant (c == m && w == 6) || w == c + 1;
  loop assigns w, c;
*/
while (c>0) {
      w = w-w;
      w = w+c;
      c = c-1;
  }

}
