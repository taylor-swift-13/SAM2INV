int main1(int z,int b){
  int si, r, n, v4x;

  si=z+25;
  r=0;
  n=0;
  v4x=0;

  while (1) {
      if (!(v4x<si)) {
          break;
      }
      n += z;
      b += r;
      v4x += 1;
  }

  while (v4x<si) {
      v4x += 1;
      n += z;
      z += r;
  }

}
