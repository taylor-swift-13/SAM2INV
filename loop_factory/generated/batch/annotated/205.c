int main1(int n,int q){
  int m, k, x, v;

  m=(q%6)+4;
  k=0;
  x=k;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 0;
  loop invariant m == (\at(q,Pre) % 6) + 4;
  loop invariant x == v - 8;
  loop invariant v >= 8;
  loop invariant n == \at(n,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant (k < m/2 ==> x == v - 8) && v >= 8 && v % 8 == 0;


  loop invariant m == (q % 6) + 4;
  loop invariant v > 0;
  loop invariant x >= 0;

  loop assigns x, v;
*/
while (k+3<=m) {
      if (k<m/2) {
          x = x+v;
      }
      else {
          x = x+1;
      }
      v = v+v;
  }

}
