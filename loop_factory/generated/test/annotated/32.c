int main1(int n){
  int f, ru;
  f=0;
  ru=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0;
  loop invariant n == \at(n,Pre);
  loop invariant (ru == 0) || (ru == \at(n,Pre));
  loop assigns ru, n;
*/
while (ru!=0&&ru!=0) {
      if (ru>ru) {
          ru = ru - ru;
      }
      else {
          ru = ru - ru;
      }
      n += f;
  }
}