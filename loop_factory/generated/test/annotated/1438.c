int main1(){
  int p5es, ya, ypi, w78;
  p5es=69;
  ya=p5es;
  ypi=ya;
  w78=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ya >= p5es;
  loop invariant ya == p5es + w78;
  loop invariant w78 <= 0;
  loop assigns w78, ya, ypi;
*/
while (ya > p5es) {
      ya = ya - 1;
      w78 = w78 - 1;
      ypi += ya;
  }
}