int main1(int v,int u){
  int m2, eh4, x3e;
  m2=(u%26)+19;
  eh4=0;
  x3e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x3e;
  loop invariant eh4 == x3e * v;
  loop invariant m2 == (u % 26) + 19;
  loop invariant (m2 <= 0) || (x3e <= m2);
  loop assigns x3e, eh4;
*/
while (1) {
      if (!(x3e<m2)) {
          break;
      }
      x3e += 1;
      eh4 += v;
  }
}