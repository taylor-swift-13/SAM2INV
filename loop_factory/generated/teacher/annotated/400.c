int main1(int k,int p){
  int b, w, v, e;

  b=(k%33)+7;
  w=b+3;
  v=b;
  e=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(k, Pre) % 33 + 7;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant 4*v + w*w + 2*w == b*b + 12*b + 15;

  loop invariant w <= b + 3;
  loop invariant w >= b - 1;


  loop invariant w <= (\at(k, Pre) % 33 + 10);
  loop invariant (w - b) % 2 == 1 || (w - b) % 2 == -1;
  loop invariant b == (k % 33) + 7;

  loop assigns v, w;
*/
while (w>b) {
      v = v+w;
      w = w-2;
  }

}
