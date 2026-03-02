int main1(int k,int p){
  int b, u, v;

  b=p;
  u=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b == p;
  loop invariant u >= 0;
  loop invariant (u == 0) ==> (v == p);
  loop invariant (u > 0) ==> (v >= 0);
  loop invariant p == \at(p, Pre) && b == p && u >= 0 && (u == 0 ==> v == p);
  loop invariant v >= p;
  loop invariant u >= 0 && (u == 0) ==> (v == p) && v >= p;
  loop invariant b == \at(p, Pre);
  loop invariant \at(p, Pre) == 0 ==> v == 0;
  loop invariant k == \at(k,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant b == \at(p,Pre);
  loop invariant (u == 0 ==> v == p) && (u >= 1 ==> v >= 0);
  loop invariant k == \at(k, Pre) && p == \at(p, Pre) && b == p && u >= 0;
  loop invariant b == \at(p, Pre) && p == \at(p, Pre) && k == \at(k, Pre)
                   && u >= 0 && ((v == 0) <==> (p == 0));
  loop invariant b == \at(p, Pre) && k == \at(k, Pre) && u >= 0;
  loop invariant u == 0 ==> v == b;
  loop invariant b == p && k == \at(k, Pre) && p == \at(p, Pre) && u >= 0;
  loop invariant (u == 0 ==> v == p) && (u > 0 ==> v >= 0);
  loop assigns u, v;
*/
while (1) {
      v = v*v;
      u = u+1;
  }

}
