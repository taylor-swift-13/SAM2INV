int main1(int a,int k,int n,int q){
  int h, o, v, i;

  h=(k%8)+14;
  o=0;
  v=h;
  i=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == h + o*(3 + 2*i);
  loop invariant 0 <= o;
  loop invariant o <= h;
  loop invariant i == k;
  loop invariant h == (k % 8) + 14;
  loop invariant v == h + o * (2*i + 3);
  loop invariant o >= 0;
  loop assigns o, v;
*/
while (1) {
      if (o>=h) {
          break;
      }
      v = v+3;
      o = o+1;
      v = v+i+i;
  }

}
