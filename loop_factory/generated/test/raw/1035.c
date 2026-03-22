int main1(){
  int uw, lx, xd5t, jec, oy;

  uw=(1%14)+4;
  lx=0;
  xd5t=1;
  jec=0;
  oy=0;

  while (xd5t<=uw) {
      jec = jec+2*xd5t-1;
      xd5t += 1;
      oy += jec;
  }

  while (1) {
      oy++;
      if (oy>=lx) {
          break;
      }
  }

}
