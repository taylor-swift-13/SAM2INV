int main1(int m,int q){
  int e, u, j, v;

  e=(m%15)+8;
  u=0;
  j=m;
  v=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (m % 15) + 8;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (j > v) ==> (j - v + 4 >= 0);
  loop invariant (j <= v) ==> (v - j >= 0);
  loop assigns j, v;
*/
while (j!=0&&v!=0) {
      if (j>v) {
          j = j-v;
      }
      else {
          v = v-j;
      }
      j = j+4;
  }

}
