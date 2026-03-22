int main1(){
  int z4u, qmx, fi;
  z4u=1+8;
  qmx=1;
  fi=qmx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qmx <= z4u;
  loop invariant (qmx % 2) == 1;
  loop invariant fi > 0;
  loop invariant z4u == 9;
  loop assigns fi, qmx;
*/
while (qmx+2<=z4u) {
      fi = fi + fi;
      qmx += 2;
  }
}