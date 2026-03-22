int main1(int z){
  int sca, mox, sd, j;
  sca=z;
  mox=sca;
  sd=mox;
  j=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sca == z;
  loop invariant ( (j == -1) || (j == 0) );
  loop invariant ( (j != -1) ==> (sd % 3 == 0) );
  loop invariant (z - mox) >= 0;
  loop invariant ((z - mox) % 3) == 0;
  loop invariant sca == \at(z, Pre);
  loop invariant (j <= 0);
  loop assigns sd, j, mox;
*/
while (mox-3>=0) {
      sd = sd*3;
      j = j/3;
      mox = mox - 3;
  }
}