#! /usr/bin/env bash

printf "Build Releases\n"
printf "==============\n\n"

version=$(\
    cargo metadata --format-version=1 --offline --no-deps \
    | jq -r '.packages[] | select ( .name == "sqlgen").version' \
)

printf "Version: $version\n\n"

targets=(
    "aarch64-apple-darwin:nocross:noext"
    "x86_64-apple-darwin:nocross:noext"
    "x86_64-unknown-linux-gnu:cross:noext"
    "x86_64-pc-windows-gnu:cross:.exe"
)

printf "Plan:\n"
for target in ${targets[@]}; do
    printf "\t$(echo $target | cut -d ":" -f 1)\n"
    printf "\t\t:: $(echo $target | cut -d ":" -f 2)\n"
    printf "\t\t:: $(echo $target | cut -d ':' -f 3)\n"
done

printf "\n==============\n\n"

logdir=$HOME/.build-releases
log=$logdir/log

mkdir -p $logdir

# truncate log file
echo -n > $log

outdir=$HOME/sqlgen-releases/$version

mkdir -p $outdir

for target in ${targets[@]}; do
    triple=$(echo $target | cut -d ":" -f 1)
    usecross=$(echo $target | cut -d ":" -f 2)
    ext=$(echo $target | cut -d ":" -f 3)

    echo $triple >> $log
    echo "------" >> $log

    if [ $usecross = "nocross" ]; then
        printf "Building for target $triple using cargo, this might take a while...\n"
        cargo build --release --target $triple &>>$log
    else
        printf "Building for target $triple using cross, this might take a while...\n"
        cross build --release --target $triple &>>$log
    fi

    if [ $? == 0 ]; then
        printf "Build completed\n"
        echo "" >> $log

        if [ $ext = "noext" ]; then
            executable="./target/${triple}/release/sqlgen"
            out="${outdir}/sqlgen_${version}_${triple}"
        else
            executable="./target/${triple}/release/sqlgen${ext}"
            out="${outdir}/sqlgen_${version}_${triple}${ext}"
        fi

        mv $executable $out

        printf "Built executable available at\n"
        printf "\t$out\n"
    else
        printf "Build failed - logs are available at:\n"
        printf "\t$log\n"
        exit -127
    fi
done


printf "Finished!\n"

