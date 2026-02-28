int main1(int k,int m){
  int o, x, v, w, u;

  o=m;
  x=0;
  v=8;
  w=k;
  u=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 8 + x*(w+u);
  loop invariant o == m;
  loop invariant w == k;
  loop invariant u == -8;
  loop invariant 0 <= x;
  loop invariant x <= o || o <= 0;
  loop invariant w == \at(k, Pre);
  loop invariant o == \at(m, Pre);

  loop invariant v == 8 + x*(k - 8);

  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);

  loop assigns v, x;
*/
while (x<o) {
      v = v+w+u;
      x = x+1;
  }

}
