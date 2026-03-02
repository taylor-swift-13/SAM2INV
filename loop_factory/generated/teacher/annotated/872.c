int main1(int k,int p){
  int o, l, v, c;

  o=(k%7)+20;
  l=0;
  v=0;
  c=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == k * c;
  loop invariant c <= o;
  loop invariant o == (k % 7) + 20;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == c * k;
  loop invariant v == c * k && o == (k % 7) + 20;
  loop invariant 0 <= c;
  loop invariant 0 <= c && c <= o;
  loop invariant 0 <= c <= o;
  loop assigns c, v;
*/
while (c<o) {
      v = v+k;
      c = c+1;
  }

}
