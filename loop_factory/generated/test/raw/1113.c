int main1(int y,int x){
  int e5, m, ju, sflb, les, pz, gt;

  e5=x;
  m=0;
  ju=y;
  sflb=0;
  les=m;
  pz=e5;
  gt=6;

  while (1) {
      if (!(m+1<=e5)) {
          break;
      }
      gt = gt + m;
      sflb = sflb+ju*m;
      e5 = (m+1)-1;
  }

  while (1) {
      if (!(pz<=les-1)) {
          break;
      }
      gt = gt + y;
      pz = pz + 1;
      ju = ju + gt;
  }

}
