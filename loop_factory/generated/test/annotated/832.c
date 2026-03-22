int main1(){
  int g, g83, e, k98u, a0, pbbd;
  g=1;
  g83=-5;
  e=g;
  k98u=g83;
  a0=g;
  pbbd=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a0 <= g;
  loop invariant g == 1;
  loop invariant k98u <= -5;
  loop invariant e >= 1;
  loop invariant pbbd >= 3;
  loop assigns k98u, e, a0, pbbd;
*/
while (a0<g) {
      k98u = k98u*pbbd;
      e = e*pbbd+4;
      a0++;
      pbbd = pbbd+(e%9);
      pbbd = pbbd*2;
  }
}