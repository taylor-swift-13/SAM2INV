int main1(){
  int j7, x4x, mjk, u, j;

  j7=1;
  x4x=0;
  mjk=(1%40)+2;
  u=0;
  j=x4x;

  while (mjk!=u) {
      u = mjk;
      mjk = (mjk+j7/mjk)/2;
      j = j+(mjk%6);
  }

}
