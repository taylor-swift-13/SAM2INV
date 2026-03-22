int main1(){
  int vhk, el, ym, net, vq;

  vhk=1+8;
  el=vhk+4;
  ym=-5;
  net=4;
  vq=vhk;

  while (1) {
      if (!(el-vhk>0)) {
          break;
      }
      net = net+ym*el;
      vq = vq + net;
      ym += 1;
      vhk = 0;
  }

  while (net<=ym-1) {
      vhk = vhk + vq;
      vq = vq + net;
      net = ym;
  }

}
