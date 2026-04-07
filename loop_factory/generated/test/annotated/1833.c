int main1(){
  int xup, zi, yss, h1, fc1k;
  xup=1*2;
  zi=xup+5;
  yss=5;
  h1=-3;
  fc1k=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((zi == 7) || (zi == 1));
  loop invariant ((fc1k == 0 && h1 == -3 && yss == 5 && zi == 7 && xup == 2) ||
                     (fc1k == 7 && h1 == -2 && yss == 4 && zi == 1 && xup == 2));
  loop invariant ((zi == 7 && h1 == -3 && fc1k == 0 && yss == 5) ||
                     (zi == 1 && h1 == -2 && fc1k == 7 && yss == 4));
  loop invariant ((zi == 7 && fc1k == 0) || (zi == 1 && fc1k == 7));
  loop invariant (h1 == -3 || h1 == -2);
  loop invariant (yss == 5 || yss == 4);
  loop invariant (fc1k == 0 || fc1k == 7);
  loop assigns h1, fc1k, yss, zi;
*/
while (zi>1) {
      h1 = h1 + 1;
      fc1k = fc1k + zi;
      yss = h1*h1;
      zi = 1;
  }
}