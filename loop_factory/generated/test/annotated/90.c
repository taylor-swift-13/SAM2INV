int main1(int t,int e){
  int ll, y, lu, cotj;
  ll=e*3;
  y=0;
  lu=0;
  cotj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lu == cotj % 3;
  loop invariant t == \at(t, Pre) + cotj * (y + 1);
  loop invariant ll == 3 * \at(e,Pre);
  loop invariant y == 0;
  loop invariant (ll < 0) || (0 <= cotj && cotj <= ll);
  loop invariant 0 <= cotj;
  loop assigns cotj, t, lu;
*/
while (1) {
      if (!(cotj<=ll-1)) {
          break;
      }
      cotj = cotj + 1;
      t = t + y;
      lu = (lu+1)%3;
      t += 1;
  }
}