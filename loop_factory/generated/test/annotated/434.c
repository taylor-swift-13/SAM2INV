int main1(int e){
  int a, a7, pq, u;
  a=(e%19)+6;
  a7=a;
  pq=0;
  u=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(e, Pre) + 2 * ((pq / 4) * ((pq / 4) + 1));
  loop invariant pq % 4 == 0;
  loop invariant 0 <= pq;
  loop invariant a == (\at(e, Pre) % 19) + 6;
  loop assigns e, pq, u;
*/
while (pq<a) {
      u = (a)+(-(pq));
      pq += 4;
      e = e + pq;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a7 <= a;
  loop invariant a <= a7;
  loop invariant a == (\at(e, Pre) % 19) + 6;
  loop assigns a7;
*/
while (1) {
      if (!(a7<=a-1)) {
          break;
      }
      a7 += 1;
  }
}