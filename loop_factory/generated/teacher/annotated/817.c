int main1(int b,int p){
  int u, w, v, f;

  u=b;
  w=2;
  v=-5;
  f=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == b;
  loop invariant w >= 2;

  loop invariant w >= 2 && ((w > 2) ==> (v == u + 2*w - 2));
  loop invariant (w > 2) ==> (v == u + 2*(w - 1));
  loop invariant (w == 2) ==> (v == -5);
  loop invariant (w == 2) ==> (f == 2);
  loop invariant (w >= 3) ==> (v == b + 2*w - 2);
  loop assigns v, f, w;
*/
while (1) {
      v = v+1;
      f = f+v;
      v = u+w;
      f = f+v;
      v = v+w;
      w = w+1;
  }

}
