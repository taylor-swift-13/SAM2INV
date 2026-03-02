int main1(int k,int p){
  int l, w, v;

  l=69;
  w=l;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (69 - w) % 4 == 0;
  loop invariant w <= 69;
  loop invariant w >= 1;
  loop invariant l == 69;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant w % 4 == 1;
  loop invariant l == 69 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant w <= 69 && (69 - w) % 4 == 0 && w >= 1;
  loop invariant k == \at(k, Pre) && p == \at(p, Pre) && l == 69;
  loop invariant 1 <= w && w <= 69 && (69 - w) % 4 == 0;
  loop invariant w <= 69 && w % 4 == 1;

  loop invariant (w - 69) % 4 == 0;
  loop invariant (w % 4 == 1) && (w <= 69) && (w >= 1) && (v >= p) && (k == \at(k, Pre)) && (p == \at(p, Pre));
  loop invariant (l == 69);
  loop invariant w <= l;
  loop invariant w % 4 == l % 4;
  loop assigns v, w;
*/
while (w>3) {
      v = v*v;
      w = w-4;
  }

}
