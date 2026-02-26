int main1(int k,int p){
  int l, w, v;

  l=69;
  w=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 69;
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant w % 4 == 0;
  loop invariant w >= 0;
  loop invariant l - w >= 0;

  loop invariant v >= -1;
  loop invariant v < l - 1;
  loop invariant 0 <= w;
  loop invariant w <= l;
  loop invariant v <= w;
  loop invariant -1 <= v;
  loop invariant 0 <= w <= l - 1;
  loop invariant v < l;
  loop assigns v, w;
*/
while (w+4<=l) {
      if (v+1<l) {
          v = v-v;
      }
      v = v+v;
      v = v+w;
      w = w+4;
  }

}
