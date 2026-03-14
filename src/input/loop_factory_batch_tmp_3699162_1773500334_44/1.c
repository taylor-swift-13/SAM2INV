int main1(){
  int iys, r8dx, ut, bqk;

  iys=1*2;
  r8dx=2;
  ut=iys;
  bqk=0;

  while (1) {
      if (!(r8dx<=iys-1)) {
          break;
      }
      bqk = bqk+ut*r8dx;
      ut = ut + iys;
      r8dx = iys;
  }

  while (ut<=iys-1) {
      bqk = bqk + 1;
      ut += 1;
  }

}
