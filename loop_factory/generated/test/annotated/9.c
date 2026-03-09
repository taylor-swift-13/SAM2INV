int main1(int q){
  int sr, nm, k;
  sr=18;
  nm=3;
  k=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*k == (nm - 3) * (nm + 4*q + 4);
  loop invariant 3 <= nm <= sr;
  loop invariant k == ((nm - 3) * (nm - 2)) / 2 + (nm - 3) * (3 + 2 * q);
  loop invariant k == (nm*nm + (4*q + 1)*nm - 12*(q + 1)) / 2;
  loop invariant k == (nm*(nm+1))/2 + 2*q*nm - 6 - 6*q;
  loop invariant 3 <= nm && nm <= sr;
  loop invariant k == (nm - 3) * (2 * q + 4) + ((nm - 3) * (nm - 4)) / 2;
  loop invariant 3 <= nm;
  loop invariant nm <= sr;
  loop assigns k, nm;
*/
while (nm<=sr-1) {
      nm = nm + 1;
      k = k + nm;
      k = k+q+q;
  }
}