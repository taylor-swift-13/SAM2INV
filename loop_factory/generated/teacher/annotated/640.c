int main1(int m,int p){
  int z, x, v, h;

  z=p;
  x=3;
  v=z;
  h=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h >= p;
  loop invariant z == p;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (v == h) || (v == h - 2);
  loop invariant (h - p) % 7 == 0;
  loop invariant ((h - v) == 0) || ((h - v) == 2);
  loop invariant ((v - h) == 0) || ((v - h) == -2);
  loop invariant ((h - p) % 7) == 0;
  loop invariant (h - v) % 2 == 0;

  loop assigns v, h;
*/
while (1) {
      v = v+8;
      h = h+8;
      v = v+1;
      h = h-1;
      v = h-v;
      v = v+h;
  }

}
