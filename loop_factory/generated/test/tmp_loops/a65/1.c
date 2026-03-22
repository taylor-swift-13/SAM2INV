int main1(int e,int v){
  int pqg8, f, bn, e1s, x70, of5, r0sl;

  pqg8=0;
  f=(v%20)+10;
  bn=(v%15)+8;
  e1s=8;
  x70=-1;
  of5=-6;
  r0sl=pqg8;

  while (f>0&&bn>0) {
      if (pqg8%2==0) {
          f--;
      }
      else {
          bn -= 1;
      }
      pqg8 = pqg8 + 1;
      if (!(!((pqg8%4)==0))) {
          x70 += of5;
      }
      of5 += bn;
      e1s += 2;
      of5 += 1;
      v = e-v;
      if ((pqg8%7)==0) {
          r0sl = r0sl + e;
      }
      e += v;
  }

}
