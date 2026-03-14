int main1(){
  int ll, zv, jcz, lc, j, z0ub;

  ll=1;
  zv=ll;
  jcz=3;
  lc=0;
  j=0;
  z0ub=zv;

  while (lc<=ll-1) {
      lc = lc + 1;
      jcz = jcz + 1;
      z0ub = z0ub + jcz;
      j = j*3+1;
  }

  while (1) {
      if (jcz%2==0) {
          lc += j;
      }
      else {
          lc = lc+j+1;
      }
      j = j + jcz;
      jcz = jcz + 1;
      if (jcz>=ll) {
          break;
      }
  }

}
