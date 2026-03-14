int main1(int t,int u){
  int uh, bjc, j, tp56, f86;
  uh=(u%38)+4;
  bjc=uh;
  j=0;
  tp56=0;
  f86=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j % 4 == 0);
  loop invariant uh == \at(u, Pre) % 38 + 4;
  loop invariant f86 >= u;
  loop invariant (0 <= j);
  loop invariant ((j == 0) ==> (tp56 == 0));
  loop invariant ((j > 0) ==> (tp56 == j - 2));
  loop assigns f86, j, tp56;
*/
while (j<=uh-1) {
      tp56 = j+2;
      j += 4;
      f86 = f86 + tp56;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t >= \at(t, Pre));
  loop invariant bjc == \at(u, Pre) % 38 + 4;
  loop invariant 0 <= tp56;
  loop assigns f86, tp56, t;
*/
while (tp56<bjc) {
      f86 += t;
      tp56 += 1;
      t = t + tp56;
  }
}