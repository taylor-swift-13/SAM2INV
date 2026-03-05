int main68(int z,int h,int c){
  int byue, j1, v, b, mz, y;

  byue=c;
  j1=(c%40)+2;
  v=0;
  b=0;
  mz=c*4;
  y=3;

  while (1) {
      if (!(j1!=v)) {
          break;
      }
      v = j1;
      b = b+(v%2);
      j1 = (j1+byue/j1)/2;
      b = b + mz;
      h = h+j1-v;
      mz = mz + y;
  }

}
