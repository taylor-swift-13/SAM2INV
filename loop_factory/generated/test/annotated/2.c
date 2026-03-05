int main1(int p,int q){
  int c, j1;
  c=0;
  j1=(q%15)+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 0;
  loop invariant q == \at(q, Pre);
  loop invariant j1 <= (\at(q, Pre) % 15) + 3;
  loop invariant p == \at(p, Pre) + ((\at(q, Pre) % 15) + 3 - j1) * c;
  loop assigns p, j1;
*/
while (j1!=0) {
      j1 = j1 - 1;
      p = p + c;
  }
}