int main1(int b,int k,int m,int q){
  int o, j, w, v;

  o=q;
  j=o;
  w=2;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j <= o;
  loop invariant w == 2 + 5*(j - o);
  loop invariant o == q;
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= j - o;
  loop invariant j - o <= 1;
  loop invariant m == \at(m, Pre);
  loop invariant w - 5 * j == 2 - 5 * \at(q, Pre);
  loop assigns w, j;
*/
while (1) {
      if (j>=o) {
          break;
      }
      w = w+1;
      j = j+1;
      w = w+4;
  }

}
