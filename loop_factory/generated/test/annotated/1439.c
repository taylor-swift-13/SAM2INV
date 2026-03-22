int main1(){
  int hp9s, ze5, ow, vvyq, ljt;
  hp9s=1*5;
  ze5=0;
  ow=vvyq + ljt;
  vvyq=0;
  ljt=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hp9s == 5;
  loop invariant 0 <= ze5 <= hp9s;
  loop assigns ze5, ow, vvyq;
*/
while (1) {
      if (!(ze5 < hp9s)) {
          break;
      }
      ze5 = ze5 + 1;
      ow = vvyq + ljt - ze5;
      vvyq += ze5;
  }
}