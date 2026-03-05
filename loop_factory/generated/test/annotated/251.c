int main1(){
  int n7, txx, mxs;
  n7=1;
  txx=n7;
  mxs=n7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n7 == 1;
  loop invariant txx == 1;
  loop invariant mxs >= n7;
  loop invariant mxs <= 2*n7;
  loop invariant mxs == 1 || mxs >= 2*n7;
  loop invariant mxs >= 1;
  loop assigns mxs;
*/
while (txx>=3) {
      if (mxs+6<=n7) {
          mxs += 6;
      }
      else {
          mxs = n7;
      }
      mxs = mxs + n7;
  }
}