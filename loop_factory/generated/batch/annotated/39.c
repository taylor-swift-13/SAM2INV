int main1(int a,int q){
  int j, u, v, g, e, r;

  j=a;
  u=0;
  v=a;
  g=q;
  e=j;
  r=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == a && g == q && e == a && j == a && v == e;
  loop invariant u >= 0;
  loop invariant j == \at(a, Pre);
  loop invariant v == \at(a, Pre) && g == \at(q, Pre) && e == j;

  loop invariant u > 0 ==> r == v + g + e;
  loop invariant j == a;
  loop invariant ((u == 0) ==> (r == u)) && ((u > 0) ==> (r == v + g + e)) && (v == a) && (g == q) && (e == j);
  loop invariant j == a && v == a && e == a && 0 <= u && (u == 0 ==> r == 0) && (u > 0 ==> r == v + g + e);
  loop invariant a == \at(a,Pre);
  loop invariant 0 <= u;
  loop invariant j < 0 || u <= j;
  loop invariant (u > 0) ==> r == v + g + e;
  loop invariant e == j;
  loop invariant v == j;
  loop invariant g == \at(q, Pre);
  loop assigns r, u;
*/
while (u<j) {
      r = v+g+e;
      u = u+1;
  }

}
