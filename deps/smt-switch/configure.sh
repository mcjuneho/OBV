#!/bin/sh

# Syntax and structure borrowed from CVC4's configure.sh script

CONF_FILE=Makefile.conf

usage () {
cat <<EOF
Usage: $0 [<option> ...]

Configures the CMAKE build environment.

-h, --help              display this message and exit
--prefix=STR            install directory       (default: /usr/local/)
--btor                  build boolector         (default: off)
--yices2                build yices2            (default: off)
--cvc4                  build cvc4              (default: off)
--msat                  build MathSAT           (default: off)
--btor-home=STR         custom BTOR location    (default: deps/boolector)
--yices2-home=STR       custom YICES2 location  (default: deps/yices2)
--cvc4-home=STR         custom CVC4 location    (default: deps/CVC4)
--msat-home=STR         custom MathSAT location (default: deps/mathsat)
--build-dir=STR         custom build directory  (default: build)
--debug                 build debug with debug symbols (default: off)
--static                create static libaries (default: off)
--python                compile with python bindings (default: off)
--py2                   use python2 interpreter (default: python3)
EOF
  exit 0
}

die () {
    echo "*** $0: $*" 1>&2
    exit 1
}

build_dir=build
install_prefix=default
build_btor=default
build_yices2=default
build_cvc4=default
build_msat=default
btor_home=default
yices2_home=default
cvc4_home=default
msat_home=default
static=default
python=default
py2=default

build_type=Release

while [ $# -gt 0 ]
do
    case $1 in
        -h|--help) usage;;
        --prefix) die "missing argument to $1 (see -h)" ;;
        --prefix=*)
            install_prefix=${1##*=}
            # Check if install_prefix is an absolute path and if not, make it
            # absolute.
            case $install_prefix in
                /*) ;;                                      # absolute path
                *) install_prefix=$(pwd)/$install_prefix ;; # make absolute path
            esac
            ;;
        --btor)
            build_btor=ON
            ;;
        --yices2)
            build_yices2=ON
            ;;
        --cvc4)
            build_cvc4=ON
            ;;
        --msat)
            build_msat=ON
            ;;
        --btor-home) die "missing argument to $1 (see -h)" ;;
        --btor-home=*)
            btor_home=${1##*=}
            # Check if btor_home is an absolute path and if not, make it
            # absolute.
            case $btor_home in
                /*) ;;                                      # absolute path
                *) btor_home=$(pwd)/$btor_home ;; # make absolute path
            esac
            ;;
        --cvc4-home) die "missing argument to $1 (see -h)" ;;
        --cvc4-home=*)
            cvc4_home=${1##*=}
            # Check if cvc4_home is an absolute path and if not, make it
            # absolute.
            case $cvc4_home in
                /*) ;;                                      # absolute path
                *) cvc4_home=$(pwd)/$cvc4_home ;; # make absolute path
            esac
            ;;
        --msat-home) die "missing argument to $1 (see -h)" ;;
        --msat-home=*)
            msat_home=${1##*=}
            # Check if msat_home is an absolute path and if not, make it
            # absolute.
            case $msat_home in
                /*) ;;                                      # absolute path
                *) msat_home=$(pwd)/$msat_home ;; # make absolute path
            esac
            ;;
        --yices2-home) die "missing argument to $1 (see -h)" ;;
        --yices2-home=*)
            yices2_home=${1##*=}
            # Check if yices2_home is an absolute path and if not, make it
            # absolute.
            case $yices2_home in
                /*) ;;                                      # absolute path
                *) yices2_home=$(pwd)/$yices2_home ;; # make absolute path
            esac
            ;;
        --build-dir) die "missing argument to $1 (see -h)" ;;
        --build-dir=*)
            build_dir=${1##*=}
            # Check if build_dir is an absolute path and if not, make it
            # absolute.
            case $build_dir in
                /*) ;;                                      # absolute path
                *) build_dir=$(pwd)/$build_dir ;; # make absolute path
            esac
            ;;
        --debug)
            build_type=Debug;
            ;;
        --static)
            static=yes
            ;;
        --python)
            python=yes
            ;;
        --py2)
            py2=yes
            ;;
        *) die "unexpected argument: $1";;
    esac
    shift
done

# enable solvers automatically if a custom home is provided
if [ $btor_home != default -a $build_btor = default ]; then
    build_btor=ON
fi

if [ $cvc4_home != default -a $build_cvc4 = default ]; then
    build_cvc4=ON
fi

if [ $msat_home != default -a $build_msat = default ]; then
    build_msat=ON
fi

if [ $yices2_home != default -a $build_yices2 = default ]; then
    build_yices2=ON
fi

cmake_opts="-DCMAKE_BUILD_TYPE=$build_type"

[ $install_prefix != default ] \
    && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$install_prefix"

[ $build_btor != default ] \
    && cmake_opts="$cmake_opts -DBUILD_BTOR=$build_btor"

[ $build_cvc4 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_CVC4=$build_cvc4"

[ $build_msat != default ] \
    && cmake_opts="$cmake_opts -DBUILD_MSAT=$build_msat"

[ $build_yices2 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_YICES2=$build_yices2"

[ $btor_home != default ] \
    && cmake_opts="$cmake_opts -DBTOR_HOME=$btor_home"

[ $cvc4_home != default ] \
    && cmake_opts="$cmake_opts -DCVC4_HOME=$cvc4_home"

[ $msat_home != default ] \
    && cmake_opts="$cmake_opts -DMSAT_HOME=$msat_home"

[ $yices2_home != default ] \
    && cmake_opts="$cmake_opts -DYICES2_HOME=$yices2_home"

[ $static != default ] \
    && cmake_opts="$cmake_opts -DSMT_SWITCH_LIB_TYPE=STATIC"

[ $python != default ] \
    && cmake_opts="$cmake_opts -DBUILD_PYTHON_BINDINGS=ON"

[ $py2 != default ] \
    && cmake_opts="$cmake_opts -DUSE_PYTHON2=ON"

root_dir=$(pwd)

[ -e "$build_dir" ] && rm -r "$build_dir"

mkdir -p "$build_dir"
cd "$build_dir" || exit 1

[ -e CMakeCache.txt ] && rm CMakeCache.txt

echo "Running with cmake options: $cmake_opts"

cmake "$root_dir" $cmake_opts 2>&1
