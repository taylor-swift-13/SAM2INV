int main1(int a,int v){
  int p, fj, x, eft;
  p=0;
  fj=0;
  x=(a%28)+10;
  eft=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == ((\at(a,Pre) % 28) + 10) - (fj * (fj - 1)) / 2;
  loop invariant 0 <= fj <= 9;
  loop invariant 0 <= eft <= 4*fj;
  loop invariant p == 0;
  loop invariant a == \at(a,Pre);
  loop invariant v == \at(v,Pre);
  loop assigns x, eft, fj;
*/
while (x>fj) {
      x -= fj;
      eft = eft+(x%5);
      fj++;
  }
}