int main1(int k,int q){
  int t, qs, ww, hg6a, eks;
  t=0;
  qs=0;
  ww=(k%28)+10;
  hg6a=0;
  eks=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eks == hg6a;
  loop invariant eks == qs*(qs+1)/2;
  loop invariant ww == ((\at(k,Pre) % 28) + 10) - ((qs * (qs - 1)) / 2);
  loop invariant ww == ((k % 28) + 10) - (qs * (qs - 1)) / 2;
  loop invariant 0 <= qs;
  loop assigns ww, qs, eks, hg6a;
*/
while (ww>qs) {
      ww -= qs;
      qs = qs + 1;
      eks += qs;
      hg6a += qs;
  }
}