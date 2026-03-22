int main1(int a){
  int yx6, r7u, arl, pw7, l, a6;
  yx6=a;
  r7u=yx6;
  arl=0;
  pw7=0;
  l=20;
  a6=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r7u == yx6;
  loop invariant yx6 == a;
  loop invariant l >= 20;
  loop invariant pw7 >= 0;
  loop invariant a6 >= 0;
  loop invariant a6 <= 3;
  loop invariant arl == a * pw7;
  loop assigns arl, l, pw7, a6;
*/
while (1) {
      if (!(pw7<yx6)) {
          break;
      }
      arl = arl + a;
      l = l+yx6-r7u;
      pw7++;
      l = l*4+3;
      a6 = a6*l+3;
      a6 = a6%4;
  }
}